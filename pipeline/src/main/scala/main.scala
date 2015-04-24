package pipeline

import puppet.syntax._
import puppet.graph._
import scala.reflect.runtime.universe.TypeTag
import puppet.common.{resource => resrc}

import scalax.collection.Graph
import scalax.collection.GraphEdge.DiEdge
import scalax.collection.GraphEdge._
import scalax.collection.GraphPredef._
import scalax.collection.edge.Implicits._

import eval._
import eval.Implicits._

package object pipeline {

  def toFileScriptGraph(resourceGraph: ResourceGraph): FileScriptGraph = {
    nodeMap(GraphResourceToExpr, resourceGraph)
  }

  def nodeMap[A,B](f: A => B, inG: Graph[A, DiEdge])(implicit tag: TypeTag[B]): Graph[B, DiEdge] = {
    val nodeMap = inG.nodes.map(a => a -> f(a)).toMap
    val edges = inG.edges.map(edge => nodeMap(edge.from) ~> nodeMap(edge.to))
    Graph.from(nodeMap.values, edges)
  }

  def GraphResourceToExpr = toCoreResource _ andThen { ResourceToExpr(_) }

  def toCoreValue(v: Value): resrc.Value = v match {
    case UndefV => resrc.UndefV
    case StringV(s) => resrc.StringV(s)
    case BoolV(b) => resrc.BoolV(b)
    case RegexV(_) => resrc.UndefV
    case ASTHashV(_) => resrc.UndefV
    case ASTArrayV(arr) => resrc.ArrayV(arr.map(toCoreValue(_)))
    case ResourceRefV(_, _, _) => resrc.UndefV
  }

  def toCoreResource(res: puppet.graph.Resource): resrc.Resource = {
    // Rules to convert to core resource
    val attrs = res.as.filter((a) => a.value match {
      case UndefV | StringV(_) | BoolV(_) | ASTArrayV(_) => true
      case _ => false
    })
    .map((a) => (a.name, toCoreValue(a.value))).toMap

    resrc.Resource(attrs)
  }
}
