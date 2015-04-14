package pipeline.stats

import org.scalatest.FunSuite

import scalax.collection.Graph
import scalax.collection.GraphEdge._
import scalax.collection.GraphPredef._
import scalax.collection.edge.Implicits._

class AntiChainLengthTests extends FunSuite {

  test("to Poset should work 1") {

    val (set, relation) = AntiChainLength.toPoset(Graph("a" ~> "b"))
    assert(set == Set("a", "b"))
    assert(relation == Set(("a", "b")))
  }

  test("to Poset should work 2") {
    
    val (set, relation) = AntiChainLength.toPoset(Graph("a", "b"))
    assert(set == Set("a", "b"))
    assert(relation == Set.empty[(String, String)])
  }

  // TODO(nimish): more tests
}

