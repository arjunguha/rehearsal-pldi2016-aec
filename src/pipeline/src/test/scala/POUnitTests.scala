import org.scalatest.FunSuite


class POUnitTestSuite extends FunSuite {

  import scalax.collection.Graph
  import scalax.collection.GraphPredef._, scalax.collection.GraphEdge._

  test("Partial Order Width test0") {
    val g = Graph("a" ~> "b")
    assert(PartialOrderGlue.POWidth(g) == 1)
  }

  test("Partial Order Width test1") {
    val g = Graph("a" ~> "b",
                  "a" ~> "c",
                  "a" ~> "d")
    assert(PartialOrderGlue.POWidth(g) == 3)
  }

  test("Partial Order Width test2") {
    val g = Graph("a" ~> "c", "b" ~> "c", "d")
    assert(PartialOrderGlue.POWidth(g) == 3)
  }
}
