package fsmodel.ext

import fsmodel.core.Eval.{evalPred, State}
import fsmodel.core.{FileState, IsFile, IsDir, Pred}

import scalax.collection.edge.{LDiEdge}
import scalax.collection.GraphEdge.DiEdge
import scalax.collection.mutable.Graph


object Ample {

  case class Node(state: State, expr: Expr) {
    // Equality and hash-code only consider the elements in the product.
    // http://stackoverflow.com/a/5867037
    var visited = false
  }


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
        List(Node(st, Skip))
      }
      else {
        List(Node(st, Error))
      }
    }
    case If(a, p, q) => evalPred(a, st) match {
      case true => d(st, p)
      case false => d(st, q)
    }
    case Mkdir(f) => (st.get(f.getParent), st.get(f)) match {
      case (Some(IsDir), None) => List(Node(st + (f -> IsDir), Skip))
      case _ => List(Node(st, Error))
    }
    case CreateFile(f, _) => (st.get(f.getParent), st.get(f)) match {
      case (Some(IsDir), None) => List(Node(st + (f -> IsFile), Skip))
      case _ => List(Node(st, Error))
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
        Node(st1, p1) <- d1
      } yield Node(st1, Seq(p1, q))
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
        val sts1 = for (Node(st1, p1) <- d(st, p)) yield Node(st1, Concur(p1, q))
        val sts2 = for (Node(st1, q1) <- d(st, q)) yield Node(st1, Concur(p, q1))
        sts1 ++ sts2
      }
    }
  }

  def makeGraphHelper(g: MyGraph, n1: Node): Unit = {
    if (n1.visited) {
      return
    }

    n1.visited = true

    for (node <- d(n1.state, n1.expr)) {
      val n2 = g.addAndGet(node)
      g.add(DiEdge(n1, n2.value))
      makeGraphHelper(g, n2.value)
    }
  }

  def makeGraph(state: State, expr: Expr): MyGraph = {
    val g: MyGraph = Graph.empty
    val node = Node(state, expr)
    g.add(node)
    makeGraphHelper(g, node)
    g
  }

  def finalStates(init: State, expr: Expr): scala.collection.mutable.Set[State] = {
    val g = makeGraph(init, expr)
    g.nodes.filter(n => n.outDegree == 0).map(_.value.state)
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