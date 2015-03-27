import org.scalatest.FunSuite

import pipeline._

import scalax.collection.Graph
import scalax.collection.GraphEdge._
import scalax.collection.GraphPredef._
import scalax.collection.edge.Implicits._

import eval._
import eval.Implicits._

class UnitTestSuite extends FunSuite {

  val toExpr = scala.Predef.identity[Expr] _

  test("reduce empty expr graph") {
    assert(Skip == pipeline.reduceGraph(Graph.empty[Expr, DiEdge], toExpr))
  }

  test("reduce graph with one topological ordering") {
    val a = Filter(True)
    val b = Filter(False)
    assert(Skip >> Atomic(a) >> Atomic(b) == 
           pipeline.reduceGraph(Graph(a ~> b), toExpr).unconcur())
  }

  test("reduce graph with concurrent operations") {
    val a = Filter(True)
    val b = Filter(False)

    val reduced_exp = pipeline.reduceGraph(Graph(a, b), toExpr)

    // both are semantically equivalent but not syntactically
    assert(((Skip >> (Atomic(a) * Atomic(b))) == reduced_exp) ||
           ((Skip >> (Atomic(b) * Atomic(a))) == reduced_exp))
  }
}
