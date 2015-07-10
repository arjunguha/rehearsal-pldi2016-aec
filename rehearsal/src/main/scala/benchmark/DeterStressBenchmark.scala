package rehearsal

import FSSyntax._
import scala.util.Random
import java.nio.file.Paths
import java.nio.file.Path
import scalax.collection.Graph
import scalax.collection.GraphEdge.DiEdge

object DeterStressBenchmark {

  // Each expression in this stream accesses a set of locations that is disjoint from all the others in the
  // stream.
  val es: Stream[Expr] = Stream.from(0).map { n =>
    val p = Paths.get(s"/$n")
    If(TestFileState(p, IsFile), Skip, CreateFile(p, ""))
  }

  def interferingGraph(numNodes: Int, numOverlap: Int): FileScriptGraph = {
    assert(numOverlap >= 0)
    assert(numNodes >= 0)
    assert(numOverlap <= numNodes)
    val all = es.take(numNodes).toSeq
    val (overlapParts, disjoint) = all.splitAt(numOverlap)
    val overlap = overlapParts.permutations.take(numOverlap).map(es => Block(es: _*))
    Graph.from(nodes = disjoint ++ overlap, edges = List())
  }
  def run(): Unit = {

    println("Resources, Overlapping Paths, Time")

    for (nodes <- List(10, 20, 30)) { // n resources
      for (overlap <- 0 to 5) {
        val g = interferingGraph(nodes, overlap)
        val (res, t) = time(SymbolicEvaluator.isDeterministic(g))
        println(s"$nodes, $overlap, $t")

      }
    }
  }
}