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

  def evalPred(pred: Pred, s: State): Boolean = pred match {
    case True => true
    case False => false
    case And(a, b) => evalPred(a, s) && evalPred(b, s)
    case Or(a, b) =>  evalPred(a, s) || evalPred(b, s)
    case Not(a) => !evalPred(a, s)
    case TestFileState(path, expectedFileState) => s.get(path) match {
      case None => expectedFileState == DoesNotExist
      case Some(fileState) => expectedFileState == fileState
    }
  }

  def isAtomic(e: Expr): Boolean = e match {
    case Skip => true
    case Error => true
    case Atomic(_) =>  true
    case Cp(_, _) => true
    case Mkdir(_) => true
    case CreateFile(_, _) => true
    case Rm(_) => true
    case _ => false
  }

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
    case If(a, p, q) => evalPred(a, st) match {
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
    case Alt(p, q) => d(st, p) ++ d(st, q)
    case Seq(Skip, q) => d(st, q)
    case Seq(p, q) => d(st, p) match {
      case Nil => d(st, q)
      case d1 => for {
        Node(st1, p1) <- d1
      } yield Node(st1, p1 >> q)
    }
    /* Since we are dealing with atomic, intermediate states should
     * not be visible to outside world
     */
    case Atomic(p) => {

      val next_nodes =  d(st, p)

      def getTerminalNodes(nodes: List[Node],
                           terminals: List[Node]): List[Node] = nodes match {
        case Nil => terminals
        case _ => {
          val (terms, intermediates) = nodes.partition((n) => isTerminal(n.expr))
          val new_nodes = intermediates.flatMap((n) => d(n.state, n.expr))
          getTerminalNodes(new_nodes, terms ::: terminals)
        }
      }

      getTerminalNodes(next_nodes, List.empty)
    }

    case ce @Concur(p, q) => {
      if (ce.commutes) {
        d(st, p >> q)
      }
      else {
        val sts1 = for (Node(st1, p1) <- d(st, p)) yield Node(st1, p1 * q)
        val sts2 = for (Node(st1, q1) <- d(st, q)) yield Node(st1, p * q1)
        sts1 ++ sts2
      }
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