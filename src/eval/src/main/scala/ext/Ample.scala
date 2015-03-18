package fsmodel.ext

import fsmodel.core.Eval.{evalPred, State}
import fsmodel.core.{FileState, IsFile, IsDir, Pred}

import scalax.collection.edge.{LDiEdge}
import scalax.collection.GraphEdge.DiEdge
import scalax.collection.mutable.Graph


object Ample {

  type Node = (State, Expr)
  type MyGraph = Graph[Node, DiEdge]

  def isAtomic(e: Expr): Boolean = e match {
    case Skip => true
    case Error => true
    case Filter(_) => true
    case Atomic(_) =>  true
    case Cp(_, _) => true
    case Mkdir(_) => true
    case CreateFile(_, _) => true
    case Rm(_) => true
    case _ => false
  }

  def d(st: State, e: Expr): List[Node] = e match {
    case Error => List()
    case Skip => List()
    case Filter(a) => {
      if (evalPred(a, st)) {
        List(st -> Skip)
      }
      else {
        List(st -> Error)
      }
    }
    case If(a, p, q) => evalPred(a, st) match {
      case true => d(st, p)
      case false => d(st, q)
    }
    case Mkdir(f) => (st.get(f.getParent), st.get(f)) match {
      case (Some(IsDir), None) => List((st + (f -> IsDir), Skip))
      case _ => List(st -> Error)
    }
    case CreateFile(f, _) => (st.get(f.getParent), st.get(f)) match {
      case (Some(IsDir), None) => List((st + (f -> IsFile)) -> Skip)
      case _ => List(st -> Error)
    }
    case Cp(src, dst) => throw new Exception()
    case Rm(f) => throw new Exception()
    // st.get(f) match {
    //   case None => List(st -> Error)
    //   case Some(true) => st.keys.exists(k => k.getParent == f) match {
    //     case true => List(st -> Error)
    //     case false => List(st - f, Skip)
    //   }
    // }
    case Alt(p, q) => d(st, p) ++ d(st, q)
    case Seq(Skip, q) => d(st, q)
    case Seq(p, q) => d(st, p) match {
      case Nil => d(st, q)
      case d1 => for {
        (st1, p1) <- d1
      } yield (st1, Seq(p1, q))
    }
    case Atomic(p) => d(st, p)
    case (Concur(p, q)) => {
      if (Commutativity.commutes(p, q)) {
        d(st, Seq(p, q))
      }
      else if (isAtomic(p) && isAtomic(q)) {
        d(st, Alt(Seq(p, q), Seq(q, p)))
      }
      else {
        val sts1 = for ((st1, p1) <- d(st, p)) yield (st1, Concur(p1, q))
        val sts2 = for ((st1, q1) <- d(st, q)) yield (st1, Concur(p, q1))
        sts1 ++ sts2
      }
    }
  }

  def makeGraphHelper(g: MyGraph, st: State, e: Expr): Unit = {
    val n1 = st -> e
    assert(g.nodes.contains(n1))

    for (n2 <- d(st, e)) {
      val isCreated = g.add(DiEdge(n1, n2))
      if (isCreated) {
        val (st1, e1) = n2
        makeGraphHelper(g, st1, e1)
      }
    }
  }

  def makeGraph(state: State, expr: Expr): MyGraph = {
    val g: MyGraph = Graph.empty
    g.add(state -> expr)
    makeGraphHelper(g, state, expr)
    g
  }

  def finalStates(init: State, expr: Expr): scala.collection.mutable.Set[State] = {
    val g = makeGraph(init, expr)
    g.nodes.filter(n => n.outDegree == 0).map(_.value._1)
  }

  val initState = Map(java.nio.file.Paths.get("/") -> IsDir)

  def drawGraph(expr: Expr) = {
    import scalax.collection.io.dot._
    import scala.language.existentials

    //port implicits.

    val g = makeGraph(Map(java.nio.file.Paths.get("/") -> IsDir), expr)
    val root = DotRootGraph(directed=true, id =Some("Program"))

    def edgeTransformer(edge : scalax.collection.Graph[Node, DiEdge]#EdgeT) = {
      Some(root, DotEdgeStmt(edge.edge.from.toString, edge.edge.to.toString, Nil))
    }

    def nodeTransformer(node: scalax.collection.Graph[Node, DiEdge]#NodeT) = {
      Some(root, DotNodeStmt(node.toString, Nil))
    }

    val immutableG = scalax.collection.Graph.from[Node, DiEdge](g.nodes, g.edges)
    immutableG.toDot(root, edgeTransformer, None, None, Some(nodeTransformer))


  }


}