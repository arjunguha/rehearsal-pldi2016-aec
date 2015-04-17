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

  test("reduce graph with concurrent operations") {
    val a = Mkdir("/a")
    val b = Mkdir("/b")

    val reduced_exp = pipeline.reduceGraph(Graph(a, b), toExpr)

    // both are semantically equivalent but not syntactically
    assert(((Skip >> (Atomic(a) * Atomic(b))) == reduced_exp) ||
           ((Skip >> (Atomic(b) * Atomic(a))) == reduced_exp))
  }

  test("indirect concurrency 1") {
    val a = Mkdir("/a")
    val b = Mkdir("/b")
    val c = Mkdir("/c")
    val d = Mkdir("/d")
    val e = Mkdir("/e")

    val graph = Graph(DiEdge(a, b), DiEdge(c, d), DiEdge(b, e), DiEdge(d, e))
    val expr = pipeline.reduceGraph(graph, toExpr)
    assert(expr == (((Atomic(a) >> Atomic(b))*
                     (Atomic(c) >> Atomic(e))) >>
                     Atomic(e)))
  }

  test("indirect concurrency") {
    val a = Mkdir("/a")
    val q = Mkdir("/q")
    val x = Mkdir("/x")
    val p = Mkdir("/p")

    val graph = Graph(DiEdge(q, x), DiEdge(p, x), DiEdge(p, a))
    val reduced_exp = pipeline.reduceGraph(graph, toExpr)
    info(reduced_exp.toString)
    // It's still not clear what expression is compiler supposed to produce
    assert(false)
  }
}
