package pipeline.stats

import scalax.collection.Graph
import scalax.collection.GraphEdge._

private[pipeline] object AntiChainLength {

  def toPoset[N](graph: Graph[N, DiEdge]): (Set[N], Set[(N, N)]) = {
    val set = graph.nodes.map(_.value).toSet
    val relation = graph.edges.map((e) => (e.source.value, e.target.value)).toSet
    (set, relation)
  }

  def transitiveClosure[A, B](relation: Set[(A, B)]): Set[(A, B)] = {
    def addTransitive[A, B](relation: Set[(A, B)]): Set[(A, B)] = {
      relation ++ (for((x1, y1) <- relation;
                       (x2, y2) <- relation if y1 == x2) yield (x1, y2))
    }

    val tc = addTransitive(relation)
    if (tc.size == relation.size) tc
    else transitiveClosure(tc)
  }

  def toReachabilityMatrix[N](set: Set[N],
                              relation: Set[(N, N)]): Array[Array[Boolean]] = {
     val tc = transitiveClosure(relation)
     val nodes = set.toList
     var matrix = Array.fill(set.size, set.size) { false }

     tc.foreach({ case (u, v) => {
       val i = nodes.indexOf(u)
       val j = nodes.indexOf(v)

       matrix(i)(j) = true
     }})

     matrix
  }

  import ThirdParty._

  def apply[N](graph: Graph[N, DiEdge]): Int = {
    val n = graph.nodes.size
    val (set, relation) = toPoset(graph)
    val reachability_matrix = toReachabilityMatrix(set, relation)
    val m = (new BipartiteMatching(reachability_matrix)).maxBPM()
    n - m
  }
}
