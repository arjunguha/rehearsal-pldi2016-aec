package pipeline

import org.scalatest.FunSuite

import scalax.collection.Graph
import scalax.collection.GraphEdge._
import scalax.collection.GraphPredef._
import scalax.collection.edge.Implicits._

import fsmodel._
import fsmodel.ext._
import fsmodel.ext.Implicits._

class UnitTestSuite extends FunSuite {

  val toExpr = scala.Predef.identity[Expr] _

  test("reduce empty expr graph") {
    assert(Skip == pipeline.reduceGraph(Graph.empty[Expr, DiEdge], toExpr))
  }

  test("reduce graph with one topological ordering") {
    val a = Filter(core.True)
    val b = Filter(core.False)
    assert(Skip >> a >> b == 
           pipeline.reduceGraph(Graph(a ~> b), toExpr).unconcur()
                                                      .unatomic())
  }

  test("reduce graph with concurrent operations") {
    val a = Filter(core.True)
    val b = Filter(core.False)

    val reduced_exp = pipeline.reduceGraph(Graph(a, b), toExpr)
    println(reduced_exp.pretty())

    // both are semantically equivalent but not syntactically
    assert(((Skip >> (Atomic(a) * Atomic(b))) == reduced_exp) ||
           ((Skip >> (Atomic(b) * Atomic(a))) == reduced_exp))
  }
}
