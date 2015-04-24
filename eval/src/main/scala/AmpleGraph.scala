package eval

import java.nio.file.Path
import scalax.collection.edge.LDiEdge
import scalax.collection.edge.Implicits._
import scalax.collection.GraphEdge.DiEdge
import scalax.collection.mutable.Graph
import Implicits._
import puppet.graph.ResourceGraph
import scala.collection.{Seq => ScalaSeq}

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

  case class MyGraphLabel(p: ScalaSeq[R])

  type MyGraph = Graph[Node, LDiEdge]

  import scalax.collection.edge.LBase.LEdgeImplicits
  object MyGraphLabelImplicit extends LEdgeImplicits[MyGraphLabel]
  import MyGraphLabelImplicit._


  def d(st: State, g: ResourceGraph)
       (implicit toExpr: R => Expr): List[(Node, R)] = {
    val roots = g.nodes.filter(_.inDegree == 0).toList
    for {
      node <- roots
      s <- Eval.eval(toExpr(node.value), st)
    } yield (Node(s, g - node), node.value)
  }

  import scala.annotation.tailrec
  
  @tailrec
  def getBranchingState(n: Node, trace: ScalaSeq[R] = ScalaSeq.empty)
                       (implicit toExpr: R=>Expr): (Node, List[(Node, R)], ScalaSeq[R]) = {
    d(n.state, n.graph) match {
      case List() => (n, List(), trace)
      case List(n2) => getBranchingState(n2._1, trace :+ n2._2)
      case branches => (n, branches, trace)
    }
  }

  def dfs(g: MyGraph, n1: Node)
         (implicit toExpr: R=>Expr): Unit = {
    if (n1.visited) {
      return
    }

    n1.visited = true

    val (nBranch, branches, trace) = getBranchingState(n1)

    if (n1 != nBranch) {
      nBranch.visited = true
      g.add((LDiEdge(n1, nBranch)(MyGraphLabel(trace))))
    }

    for (node <- branches) {
      val n2 = g.addAndGet(node._1)
      g.add(LDiEdge(nBranch, n2.value)(node._2))
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
