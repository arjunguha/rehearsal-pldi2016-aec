package eval

import java.nio.file.Path
import scalax.collection.edge.{LDiEdge}
import scalax.collection.GraphEdge.DiEdge
import scalax.collection.mutable.Graph
import Implicits._

object Ample {

  type State = PerfMap[Path, FileState]

  case class Node(state: State, expr: Expr) {
    // Equality and hash-code only consider the elements in the product.
    // http://stackoverflow.com/a/5867037
    var visited = false

    // Cache hash code for performance reasons
    override lazy val hashCode: Int =
      runtime.ScalaRunTime._hashCode(this)
  }

  type MyGraph = Graph[Node, DiEdge]

  def isTerminal(e: Expr): Boolean = e match {
    case Skip => true
    case _ => false
  }

  def d(st: State, e: Expr): List[Node] = e match {
    case Error => {
      // throw new Exception("Error encountered")
      List()
    }
    case Skip => List()
    case If(a, p, q) => Eval.evalPred(a, st) match {
      case true => d(st, p)
      case false => d(st, q)
    }
    case Mkdir(f) => (st.get(f.getParent), st.get(f)) match {
      case (Some(IsDir), None) => List(Node(st + (f -> IsDir), Skip))
      case _ => {
        // println(s"Mkdir error: ${f.toString}")
        List(Node(st, Error))
      }
    }
    case CreateFile(f, _) => (st.get(f.getParent), st.get(f)) match {
      case (Some(IsDir), None) => List(Node(st + (f -> IsFile), Skip))
      case _ => {
        // println(s"create file error: ${f.toString}")
        List(Node(st, Error))
      }
    }
    case Cp(src, dst) => throw new Exception()
    case Rm(f) if st.contains(f) => st(f) match {
      case IsDir if st.keys.exists(_.getParent == f) => List(Node(st, Error)) // Dir should be empty to delete
      case IsFile | IsDir => List(Node(st - f, Skip))
      case _ => throw new Exception("Invalid state")
    }
    case Rm(_) => {
      // println(s"Rm error")
      List(Node(st, Error))
    }
    case Seq(Skip, q) => d(st, q)
    case Seq(p, q) => d(st, p) match {
      case Nil => d(st, q)
      case d1 => for {
        Node(st1, p1) <- d1
      } yield Node(st1, p1 >> q)
    }
  }

  def getBranchingState(n: Node): (Node, List[Node]) = {
    d(n.state, n.expr) match {
      case List() => (n, Nil)
      case List(n2) => getBranchingState(n2)
      case branches => (n, branches)
    }
  }

  def dfs(g: MyGraph, n1: Node): Unit = {
    if (n1.visited) {
      return
    }

    n1.visited = true

    val (nBranch, branches) = getBranchingState(n1)

    if (n1 != nBranch) {
      nBranch.visited = true
      g.add(DiEdge(n1, nBranch))
    }

    for (node <- branches) {
      val n2 = g.addAndGet(node)
      g.add(DiEdge(nBranch, n2.value))
      dfs(g, n2.value)
    }
  }

  def makeGraph(state: State, expr: Expr): MyGraph = {
    val g: MyGraph = Graph.empty
    val node = Node(state, expr)
    g.add(node)
    dfs(g, node)
    g
  }

  def finalStates(init: State, expr: Expr): scala.collection.mutable.Set[State] = {
    val g = makeGraph(init, expr)
    g.nodes.filter(n => n.outDegree == 0).map(_.value.state)
  }

  val initState = Map(java.nio.file.Paths.get("/") -> IsDir)

  def finalStates(g: MyGraph): Set[State] = {
    g.nodes.filter(n => n.outDegree == 0).map(_.value.state).toSet
  }
}
