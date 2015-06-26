package rehearsal

package object ppmodel {
  import puppet.graph._
  import scala.reflect.runtime.universe.TypeTag
  import scalax.collection.Graph
  import scalax.collection.GraphEdge.DiEdge
  import scalax.collection.GraphEdge._
  import scalax.collection.GraphPredef._
  import scalax.collection.edge.Implicits._

  import rehearsal.fsmodel._
  import rehearsal.fsmodel.Implicits._

  def toFileScriptGraph(resourceGraph: ResourceGraph): FileScriptGraph = {
    nodeMap((r: Resource) => ResourceToExpr(r), resourceGraph)
  }

  def nodeMap[A,B](f: A => B, inG: Graph[A, DiEdge])(implicit tag: TypeTag[B]): Graph[B, DiEdge] = {
    val nodeMap = inG.nodes.map(a => a -> f(a)).toMap
    val edges = inG.edges.map(edge => nodeMap(edge.from) ~> nodeMap(edge.to))
    Graph.from(nodeMap.values, edges)
  }

  def topologicalSort[V](graph: scalax.collection.Graph[V, DiEdge]): List[V] = {
    if (graph.isEmpty) {
      List()
    }
    else {
      graph.nodes.find(_.inDegree == 0) match {
        case None => throw CannotUpdate("cyclic graph")
        case Some(node) => {
          node :: topologicalSort(graph - node)
        }
      }
    }
  }

  def unions[A](sets: scala.Seq[Set[A]]): Set[A] = sets.foldLeft(Set[A]()) (_ union _)

}
