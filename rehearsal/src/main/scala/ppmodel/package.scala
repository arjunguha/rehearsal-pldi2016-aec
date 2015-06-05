package rehearsal

import puppet.graph._
import scala.reflect.runtime.universe.TypeTag
import puppet.common.{resource => resrc}

import scalax.collection.Graph
import scalax.collection.GraphEdge.DiEdge
import scalax.collection.GraphEdge._
import scalax.collection.GraphPredef._
import scalax.collection.edge.Implicits._

import rehearsal.fsmodel._
import rehearsal.fsmodel.Implicits._

package object ppmodel {

  def toFileScriptGraph(resourceGraph: ResourceGraph): FileScriptGraph = {
    nodeMap((r: Resource) => ResourceToExpr(r), resourceGraph)
  }

  def nodeMap[A,B](f: A => B, inG: Graph[A, DiEdge])(implicit tag: TypeTag[B]): Graph[B, DiEdge] = {
    val nodeMap = inG.nodes.map(a => a -> f(a)).toMap
    val edges = inG.edges.map(edge => nodeMap(edge.from) ~> nodeMap(edge.to))
    Graph.from(nodeMap.values, edges)
  }

}
