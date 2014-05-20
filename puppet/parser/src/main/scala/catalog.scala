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

  var nodes     = List[eval.Node] ()
  var resources = List[Resource] ()
  var overrides = List[Override] ()
  var res_orderings = List[(ResourceRefV, ResourceRefV)] ()
  var class_orderings = List [(Resource, HostClass)] ()

  type Params = List[(String, Value)]
  var classes = List [(String, Params)] ()

  private def resourceExists (res: Resource): Boolean = {
    resources.exists (_.title == res.title)
  }

  def addResource (res: Resource, parent: HostClass) {
    if (resourceExists (res)) throw new Exception ("Resource already exists")
    else { 
      resources = res :: resources
      class_orderings = (res, parent) :: class_orderings
      nodes = res :: (parent :: nodes)
    }
  }

  // TODO : Params
  def addClass (name: String, params: Params) {
    // Add only if does not exist
    if (!(classes exists (_._1 == name))) classes = (name, params) :: classes
  }

  def addOverride (filter: Filter, attrs: Attrs) {
    // Duplicates are ok as long as merge is idempotent, which it is not due to append, but again append is not supported yet
    overrides = (filter, attrs) :: overrides
  }

  def addRelationship (src: ResourceRefV, dst: ResourceRefV, refresh: Boolean = false) {
    if (refresh)
      println ("Warning: Ignoring notification. Notifications not supported (yet)")

    res_orderings = (src, dst) :: res_orderings
  }

  def findResourcesFromRef (ref: ResourceRefV): List[Resource] = {
    resources.filter (_.isReferredByRef (ref))
  }



  def toGraph (): Graph[eval.Node, DiEdge] = {

    val _edges = res_orderings.map ({ case (x, y) => 
      for (source <- findResourcesFromRef (x).asInstanceOf[List[eval.Node]]; 
           target <- findResourcesFromRef (y).asInstanceOf[List[eval.Node]]) 
        yield (source ~> target)
    })

    var edges = _edges.flatten
    val class_edges = class_orderings map ({ case (r, c) => c.asInstanceOf[eval.Node] ~> r.asInstanceOf[eval.Node] })

    edges = class_edges ::: edges
    Graph.from (nodes, edges)
  }

  def addHostClass (cl: HostClass) {
    nodes = cl :: nodes
  }
}
