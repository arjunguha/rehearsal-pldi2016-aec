import eval._
import z3analysis._
import eval.Implicits._
import scalax.collection.Graph
import scalax.collection.GraphPredef._
import scalax.collection.GraphEdge._

class DeterminismTests extends org.scalatest.FunSuite {

  test("Is a singleton graph deterministic") {
    val g = Graph[Expr, DiEdge](If(TestFileState("/foo", IsDir), Skip, Mkdir("/foo")))
    assert(Z3Evaluator.isDeterministic(g))
  }

  test("Two-node non-deterministic graph") {
    val g = Graph[Expr, DiEdge](
      Mkdir("/foo"),
      If(TestFileState("/foo", IsDir), Skip, Mkdir("/bar")))
    assert(Z3Evaluator.isDeterministic(g) == false)
  }

}
