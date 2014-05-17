package puppet.core.eval

import puppet.core._
import scalax.collection.Graph
import scalax.collection.GraphEdge._
import scalax.collection.GraphPredef._


// TODO : Consider returning "this" from some functions for function chaining
class Catalog {

  type Filter = ResourceRefV
  type Attrs = Map[String, Value]
  type Override = (Filter, Attrs)

  import scala.collection.mutable._

  var resources:   List[Resource] = List ()
  var overrides:   List[Override] = List ()
  var orderings:   List[(ResourceRefV, ResourceRefV)] = List ()

  private def resourceExists (res: Resource): Boolean = {
    resources.exists (_.title == res.title)
  }

  def addResource (res: Resource) {
    if (resourceExists (res)) throw new Exception ("Resource already exists")
    else resources = res :: resources
  }

  def addOverride (filter: Filter, attrs: Attrs) {
    // Duplicates are ok as long as merge is idempotent, which it is not due to append
    overrides = (filter, attrs) :: overrides
  }

  def addRelationship (src: ResourceRefV, dst: ResourceRefV, refresh: Boolean = false) {
    if (refresh)
      println ("Warning: Ignoring notification. Notifications not supported (yet)")

    orderings = (src, dst) :: orderings
  }

  def findResourcesFromRef (ref: ResourceRefV): List[Resource] = {
    resources.filter (_.isReferredByRef (ref))
  }

  def toGraph (): Graph[eval.Node, DiEdge] = {

    val nodes = resources

    val edges = orderings.map ({ case (x, y) => 
      for (source <- findResourcesFromRef (x).asInstanceOf[List[eval.Node]]; 
           target <- findResourcesFromRef (y).asInstanceOf[List[eval.Node]]) 
        yield (source ~> target)
    })

    Graph.from (nodes, edges.flatten)
  }
}
