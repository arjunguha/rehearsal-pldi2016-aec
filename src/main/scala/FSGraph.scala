package rehearsal

import scalax.collection.Graph
import scalax.collection.GraphEdge.DiEdge
import com.typesafe.scalalogging.LazyLogging
import Implicits._

case class ExecTree(commutingGroup: List[FSSyntax.Expr], branches: List[ExecTree]) {

  import FSSyntax._

  val fringeSize: Int = if (branches.isEmpty) 1 else branches.map(_.fringeSize).sum

  def exprs(): Expr =  ESeq(commutingGroup: _*) >> ESeq(branches.map(_.exprs()): _*)

  def size(): Int = 1 + branches.map(_.size).sum

  def isDeterministic(): Boolean = {
    val e = this.exprs()
    val sets = e.fileSets
    val ro = sets.reads
    val symb = new SymbolicEvaluatorImpl(e.paths.toList, e.hashes, ro)
    try {
      symb.isDeter(this)
    }
    finally {
      symb.free()
    }
  }

  def isDeterError(): Boolean = {
    val e = this.exprs()
    val sets = e.fileSets
    val ro = sets.reads
    val symb = new SymbolicEvaluatorImpl(e.paths.toList, e.hashes, ro)
    try {
      symb.isDeterError(this)
    }
    finally {
      symb.free()
    }
  }

}

object FSGraph {

  trait Key
  case class Labelled private[FSGraph](node: PuppetSyntax.Node, index: Int)
    extends Key
  case class Unlabelled private[FSGraph](index: Int) extends Key
  case class Derived private[FSGraph](src: Key, index: Int, label: String) extends Key

  private var i = 0

  def key(node: PuppetSyntax.Node): Key = {
    val n = i
    i = i + 1
    Labelled(node, n)
  }

  def key(): Key = {
    val n = i
    i = i + 1
    Unlabelled(n)
  }

  def derived(src: Key, label: String): Key = {
    val n = i
    i = i + 1
    Derived(src, n, label)
  }

}

// A potential issue with graphs of FS programs is that several resources may
// compile to the same FS expression. Slicing makes this problem more likely.
// To avoid this problem, we keep a map from unique keys to expressions and
// build a graph of the keys. The actual values of the keys don't matter, so
// long as they're unique. PuppetSyntax.Node is unique for every resource, so
// we use that when we load a Puppet file. For testing, the keys can be
// anything.
case class FSGraph(exprs: Map[FSGraph.Key, FSSyntax.Expr], deps: Graph[FSGraph.Key, DiEdge])
  extends LazyLogging {

  import FSGraph._

  lazy val size: Int = {
    deps.nodes.map(n => exprs(n).size).reduce(_ + _) + deps.edges.size
  }

  /** Returns an FS program that represents the action of a <b>deterministic</b> graph.
    *
    * @return an FS program
    */
  def expr(): FSSyntax.Expr = {
    FSSyntax.ESeq(deps.topologicalSort().map(k => exprs(k)): _*)
  }

  def addRoot(label: Key): FSGraph = {
    assert(!deps.nodes.contains(label))
    assert(!exprs.contains(label))
    val init = deps.nodes.filter(_.inDegree == 0).toList.map(node => DiEdge(label, node.value))
    val deps_ = deps ++ init
    FSGraph(exprs + (label -> FSSyntax.ESkip), deps_)
  }

  def exposePackageFiles(): FSGraph = {
    import FSSyntax._

    def createFile(e: Expr) = e match {
      case ECreateFile(_, _) => true
      case _ => false
    }

    def matchPackageInstall(expr: Expr): Option[(Expr, Seq[Expr])] = expr match {
      case EIf(pred@PTestFileState(p, IsFile), ESkip, seqs)
        if (p.startsWith("/packages".toPath)) => {

        val (mkdirs, mkfiles) = seqs.flatten.toList.spanRight(createFile)
        // println(s"Dirs are:\n$mkdirs\n and files are $mkfiles")
        Some((ite(pred, ESkip, ESeq(mkdirs: _*)), mkfiles.map(f => ite(pred, ESkip, f))))
      }
      case _ => None
    }

    exprs.foldLeft(FSGraph(exprs, deps)) {
      case (FSGraph(exprs, deps), (key, expr)) => {
        matchPackageInstall(expr) match {
          case Some((dirs, files)) => {
            val m = files.map(e => FSGraph.derived(key, e.toString) -> e).toMap
            // println("here: " + key)

            val edges = for (x <- m.keys; y <- deps.get(key).diSuccessors) yield { DiEdge(x, y.value) }
            val edges2 = for (x <- m.keys) yield { DiEdge(key, x) }
            // println("New edges to succs: " + edges.size + "succs " + deps.get(key).diSuccessors.map(_.value).toList)
            // println("New edges to files: " + edges2.size)
            FSGraph(exprs ++ m + (key -> dirs),  deps ++ edges ++ edges2)
          }
          case None => FSGraph(exprs, deps)
        }
      }
    }
  }

  def toExecTree(): ExecTree = {

    def loop(g: Graph[Key, DiEdge]): List[ExecTree] = {
      val fringe = g.nodes.filter(_.inDegree == 0).toList.map(_.value)
      if (fringe.isEmpty) {
        Nil
      } else {
        def f(m: Key, n: Key): Boolean = exprs(m).commutesWith(exprs(n))
        val groups = groupBy2(f, fringe)
        groups.map(group => ExecTree(group.map(k => exprs(k)), loop(g -- group)))
      }
    }

    loop(deps) match {
      case List(node) => node
      case alist => ExecTree(Nil, alist)
    }
  }

  def contractEdges(): FSGraph = {

    def isDangling(node: Graph[Key, DiEdge]#NodeT): Boolean = {
      val succs = node.diSuccessors.toSeq
      succs.length > 0 &&
        succs.forall(succ => succ.outDegree == 0 && succ.inDegree == 1) &&
        succs.combinations(2).forall {
          case Seq(node1, node2) => exprs(node1.value).commutesWith(exprs(node2.value))
        }
    }

    deps.nodes.find(isDangling _) match {
      case None => this
      case Some(node) => {
        // Must only be one of these
        val succs = node.diSuccessors.toList
        val expr_ = exprs(node.value) >> FSSyntax.ESeq(succs.map(node => exprs(node)): _*)
        logger.info(s"Contracting ${succs.map(_.value)} into ${node.value}")

        new FSGraph(
          exprs + (node.value -> expr_) -- succs.map(_.value),
          deps -- succs).contractEdges()
      }
    }
  }

  /** Prunes writes from this graph to make determinism-checking faster. */
  def pruneWrites(): FSGraph = {
    val n = allPaths.size
    val r = DeterminismPruning.pruneWrites(this)
    val m = r.allPaths.size
    logger.info(s"Pruning removed ${n - m} paths")
    r
  }

  /** Checks if two <b>deterministic</b> FS graphs are equivalent.
    *
    * @param other the other FS graph
    * @return [None] if they are equivalent and [Some cex] if they are not and [cex] witnesses the difference
    */
  def notEquiv(other: FSGraph): Option[FSEvaluator.State] = {
    SymbolicEvaluator.exprEquals(this.expr(), other.expr())
  }

  /** All paths used by the nodes of this graph. */
  lazy val allPaths = this.deps.nodes.map(n => this.exprs(n).paths)
    .foldLeft(Set.empty[Path])(_ union _)

}
