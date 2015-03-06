package pipeline.stats.ThirdParty

import org.scalatest.FunSuite

class BipartiteMatchingTests extends FunSuite {

  test("Single node should have no matching") {
    val graph = Array.fill(1, 1) {false}
    assert(0 == (new BipartiteMatching(graph)).maxBPM())
  }

  test("Slightly bigger example") {
    var matrix = Array.fill(6, 6) { false }
    matrix(0)(1) = true
    matrix(0)(2) = true
    matrix(2)(0) = true
    matrix(2)(3) = true
    matrix(3)(2) = true
    matrix(4)(2) = true
    matrix(4)(3) = true
    matrix(5)(5) = true

    assert(5 == (new BipartiteMatching(matrix)).maxBPM())
  }
}
    

