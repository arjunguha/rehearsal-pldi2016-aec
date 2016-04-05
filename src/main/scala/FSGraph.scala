package rehearsal

import scalax.collection.Graph
import scalax.collection.GraphEdge.DiEdge
import com.typesafe.scalalogging.LazyLogging
import Implicits._

sealed trait ExecTree {

  import FSSyntax._

  def exprs(): Expr = this match {
    case ETLeaf => ESkip
    case ETNode(exprs, children) => ESeq(exprs: _*) >> ESeq(children.map(_.exprs()): _*)
  }

  def size(): Int = this match {
    case ETNode(_, children) =>  1 + children.map(_.size).sum
    case ETLeaf => 0
  }

  def isDeterministic(): Boolean = {
    val e = this.exprs()
    val sets = e.fileSets
    val ro = sets.reads
    val symb = new SymbolicEvaluatorImpl(e.paths.toList, e.hashes, ro, None)
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
    val symb = new SymbolicEvaluatorImpl(e.paths.toList, e.hashes, ro, None)
    try {
      symb.isDeterError(this)
    }
    finally {
      symb.free()
    }
  }

}

case object ETLeaf extends ExecTree
case class ETNode(commutingGroup: List[FSSyntax.Expr], branches: List[ExecTree]) extends ExecTree

// A potential issue with graphs of FS programs is that several resources may
// compile to the same FS expression. Slicing makes this problem more likely.
// To avoid this problem, we keep a map from unique keys to expressions and
// build a graph of the keys. The actual values of the keys don't matter, so
// long as they're unique. PuppetSyntax.Node is unique for every resource, so
// we use that when we load a Puppet file. For testing, the keys can be
// anything.
case class FSGraph[K](exprs: Map[K, FSSyntax.Expr], deps: Graph[K, DiEdge])
  extends LazyLogging {

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

  def addRoot(label: K): FSGraph[K] = {
    assert(!deps.nodes.contains(label))
    assert(!exprs.contains(label))
    val init = deps.nodes.filter(_.inDegree == 0).toList.map(node => DiEdge(label, node.value))
    val deps_ = deps ++ init
    FSGraph(exprs + (label -> FSSyntax.ESkip), deps_)
  }

  def toExecTree(): ExecTree = {

    def loop(g: Graph[K, DiEdge]): List[ExecTree] = {
      val fringe = g.nodes.filter(_.inDegree == 0).toList.map(_.value)
      if (fringe.isEmpty) {
        Nil
      } else {
        def f(m: K, n: K): Boolean = exprs(m).commutesWith(exprs(n))
        val groups = groupBy2(f, fringe)
        groups.map(group => ETNode(group.map(k => exprs(k)), loop(g -- group)))
      }
    }

    loop(deps) match {
      case List(node) => node
      case alist => ETNode(Nil, alist)
    }
  }

  def contractEdges(): FSGraph[K] = {

    def isDangling(node: Graph[K, DiEdge]#NodeT): Boolean = {
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
  def pruneWrites(): FSGraph[K] = {
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
  def notEquiv(other: FSGraph[K]): Option[FSEvaluator.State] = {
    SymbolicEvaluator.exprEquals(this.expr(), other.expr())
  }

  /** All paths used by the nodes of this graph. */
  lazy val allPaths = this.deps.nodes.map(n => this.exprs(n).paths)
    .foldLeft(Set.empty[Path])(_ union _)

}
