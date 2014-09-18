package puppet.runtime.toposortperm

import scala.collection._
import scalax.collection.Graph
import scalax.collection.GraphEdge.DiEdge
import puppet.common._

/*
import scala.collection.immutable.Stream

case class LazyTree[T](val root: T, val children: Stream[LazyTree[T]])

// Lazy generation of recursion tree for all permutations of graph
object TopoSortPermutationLazyTree {

  private def subtrees[T](options: List[Graph[T, DiEdge]#NodeT])
                         (implicit dag: Graph[T, DiEdge]): Stream[LazyTree[T]] = options match {
    case n :: ns => new LazyTree(n.value, TopoSortPermutationLazyTree(dag - n)) #:: subtrees(ns)
    case Nil => Stream.empty
  }

  def apply[T](dag: Graph[T, DiEdge]): Stream[LazyTree[T]] =
    subtrees(dag.nodes.filter(_.inDegree == 0).toList)(dag)
}
*/


/* Lazy generation of recursion tree for all permutations of graph */
object TopoSortPermutationTree {

  private def subtrees[T](options: List[Graph[T, DiEdge]#NodeT])
                         (implicit dag: Graph[T, DiEdge]): List[Tree[T]] = options match {
    case n :: ns => new Tree(n.value, TopoSortPermutationTree(dag - n)) :: subtrees(ns)
    case Nil => List.empty
  }

  def apply[T](dag: Graph[T, DiEdge]): List[Tree[T]] =
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
