package puppet.runtime.toposortperm

import scala.collection._
import scalax.collection.Graph
import scalax.collection.GraphEdge.DiEdge

import scala.collection.immutable.Stream

class Tree[T](val root: T, val children: Stream[Tree[T]])

/* Lazy generation of recursion tree for all permutations of graph */
object TopoSortPermutationTree {

  private def subtrees[T](options: List[Graph[T, DiEdge]#NodeT])
                         (implicit dag: Graph[T, DiEdge]): Stream[Tree[T]] = options match {
    case n :: ns => new Tree(n.value, TopoSortPermutationTree(dag - n)) #:: subtrees(ns)
    case Nil => Stream.empty
  }

  def apply[T](dag: Graph[T, DiEdge]): Stream[Tree[T]] =
    subtrees(dag.nodes.filter(_.inDegree == 0).toList)(dag)
}

object GraphTopoSortPermutations {

  private def generatePermutations[N] (ord: Seq[N], subg: Graph[N,DiEdge]): Set[Seq[N]] = 
    if(subg.isEmpty) Set(ord)
    else subg.nodes.filter(_.inDegree == 0).map((n) => generatePermutations(ord :+ n.value, subg - n)).flatten

  // Returns a sequence of all topological sorts of a graph
  def apply[N](g: Graph[N, DiEdge]): Set[Seq[N]] = {
    if(g.isCyclic)
      throw new Exception("Topological sort not possible for cyclic graph")
      
    generatePermutations(Seq[N](), g)
  }
}
