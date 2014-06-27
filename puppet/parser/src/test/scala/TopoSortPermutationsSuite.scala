package test.puppet.toposortperm

import puppet.runtime.toposortperm._
import org.scalatest.FunSuite
import scalax.collection.Graph
import scalax.collection.GraphEdge.DiEdge
import scalax.collection.GraphPredef._

import scala.collection._

class TopoSortPermutationsSuite extends FunSuite {

  test("Nodes should not be missing from permuations") {

    val g = Graph.from(List('a', 'b', 'c', 'd'), Seq.empty[DiEdge[Char]])
    val perms = GraphTopoSortPermutations(g)
    assert(perms.forall(_.length == g.nodes.length))
    val isElementMissing = 
      for (p <- perms; n <- g.nodes if !(p contains n.value)) 
        yield false
    assert(!(isElementMissing contains false))
  }

  test("Graph with '5' unconnected nodes should give 120 permutations") {
    val g = Graph.from(1.to(5), Seq.empty[DiEdge[Int]])
    val perms = GraphTopoSortPermutations(g)
    assert(120 == perms.size)
  }

  test("Graph wtih '5' linearly connected nodes should give 1 permuation") {
    val g: Graph[Int, DiEdge] = Graph.from(1.to(5), Seq(1~>2, 2~>3, 3~>4, 4~>5))
    val perms = GraphTopoSortPermutations(g)
    assert(1 == perms.size)
  }
}

