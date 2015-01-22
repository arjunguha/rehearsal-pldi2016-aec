import scalax.collection.Graph
import scalax.collection.GraphEdge._

object PartialOrderGlue {

  def toPoset[N](g: Graph[N, DiEdge]): (Set[N], Set[(N, N)]) = {
    (g.nodes.map(_.value).toSet, g.edges.map((e) => (e.source.value, e.target.value)).toSet)
  }

  def toReachabilityMatrix[N](s: Set[N], r: Set[(N, N)]): Array[Array[Boolean]] = {

    val tc = TransitiveClosure(r)

    val s_list = s.toList

    var arr = Array.fill(s.size, s.size) { false }

    tc.foreach({ case (u, v) => {
      val i = s_list.indexOf(u)
      val j = s_list.indexOf(v)
      
      // Don't introduce cycles
      if(i != j) { arr(i)(j) = true }
    }})

    arr
  }

  def POWidth[N](g: Graph[N, DiEdge]): Int = {
    val n = g.nodes.size

    val (s, r) = toPoset(g)
    val reachabilility_matrix= toReachabilityMatrix(s, r)
    val m = (new BipartiteMatching(reachabilility_matrix)).maxBPM()
    n - m
  }
}
