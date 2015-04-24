package eval

import java.nio.file.Path
import scalax.collection.edge.{LDiEdge}
import scalax.collection.GraphEdge.DiEdge
import scalax.collection.mutable.Graph
import Implicits._
import puppet.graph.ResourceGraph

object AmpleGraph {

  type State = PerfMap[Path, FileState]

  // TODO(nimish) : Remove coupling on Resource Type. Type Params?
  type R = puppet.graph.Resource
  type RGNode = ResourceGraph#NodeT

  case class Node(state: State, graph: ResourceGraph) {
    // Equality and hash-code only consider the elements in the product.
    // http://stackoverflow.com/a/5867037
    var visited = false

    // Cache hash code for performance reasons
    override lazy val hashCode: Int =
      runtime.ScalaRunTime._hashCode(this)
  }

  type MyGraph = Graph[Node, DiEdge]


  def d(st: State, g: ResourceGraph)
       (implicit toExpr: R => Expr): List[Node] = {
    val roots = g.nodes.filter(_.inDegree == 0).toList
    for {
      node <- roots
      s <- Eval.eval(toExpr(node.value), st)
    } yield Node(s, g - node)
  }

  def getBranchingState(n: Node)
                       (implicit toExpr: R=>Expr): (Node, List[Node]) = {
    d(n.state, n.graph) match {
      case List() => (n, Nil)
      case List(n2) => getBranchingState(n2)
      case branches => (n, branches)
    }
  }

  def dfs(g: MyGraph, n1: Node)
         (implicit toExpr: R=>Expr): Unit = {
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

  def makeGraph(state: State, graph: ResourceGraph)
               (implicit toExpr: R=>Expr): MyGraph = {
    val g: MyGraph = Graph.empty
    val node = Node(state, graph)
    g.add(node)
    dfs(g, node)
    g
  }

  def finalStates(init: State, graph: ResourceGraph)
                 (implicit toExpr: R=>Expr): scala.collection.mutable.Set[State] = {
    val g = makeGraph(init, graph)
    g.nodes.filter(n => n.outDegree == 0).map(_.value.state)
  }

  val initState = Map(java.nio.file.Paths.get("/") -> IsDir)

  def finalStates(g: MyGraph): Set[State] = {
    g.nodes.filter(n => n.outDegree == 0).map(_.value.state).toSet
  }
}
