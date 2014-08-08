package puppet.runtime.toposortperm

import scala.collection._
import scalax.collection.Graph
import scalax.collection.GraphEdge.DiEdge

object GraphTopoSortPermutations {

  // TODO : Not Efficient, Not Tail recursive
  private def permutations[N] (ord: Seq[N], subg: Graph[N,DiEdge]): Set[Seq[N]] =
    if(subg.isEmpty) Set(ord)
    else subg.nodes.filter(_.inDegree == 0).map((n) => permutations(ord :+ n.value, subg - n)).flatten

  // TODO : Handle cycles    
  // Returns a sequence of all topological sorts of a graph
  def apply[N](g: Graph[N, DiEdge]): Set[Seq[N]] = permutations(Seq[N](), g)
}
