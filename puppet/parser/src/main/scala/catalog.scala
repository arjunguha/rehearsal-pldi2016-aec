package puppet.core.eval

import puppet.core._
import scalax.collection.Graph
import scalax.collection.GraphEdge._
import scalax.collection.GraphPredef._

class Catalog {

  type Node = eval.CatalogElement

  type Filter = ResourceRefV
  type Attrs = Map[String, Value]
  type Override = (Filter, Attrs)

  import scala.collection.mutable._

  var elements  = List[Node]()
  var klasses = List[HostClass]()
  var resources = List[Resource]()
  var overrides = List[Override]()
  var relationships = List[(ResourceRefV, ResourceRefV)]()
  var containers = List[(Resource, String)]()

  type Params = List[(String, Value)]
  var deferredClasses = List[(String, Params, String)]()
  var deferredDefines = List[(String, Params, String)]()

  private def elemExists(res: Resource): Boolean = {
    resources.exists(_.title == res.title)
  }

  def addResource(res: Resource, containedBy: String) {
    if (elemExists (res)) throw new Exception ("Resource: %s already exists".format(res.toString))
    else { 
      resources = res :: resources
      containers = (res, containedBy) :: containers
      elements = res :: elements
    }
  }

  def addClass(name: String, params: Params, containedBy: String) {
    // Add only if class does not exist already
    if (!(deferredClasses exists (_._1 == name))) deferredClasses = (name, params, containedBy) :: deferredClasses
  }

  def addDefinition(name: String, params: Params, containedBy: String) {
    // A definition can be declared mutliple times
    deferredDefines = (name, params, containedBy) :: deferredDefines
  }

  def addOverride (filter: Filter, attrs: Attrs) {
    // Duplicates are ok as long as merge is idempotent, which it is not due to append, but again append is not supported yet
    overrides = (filter, attrs) :: overrides
  }

  def addRelationship(src: ResourceRefV, dst: ResourceRefV, refresh: Boolean = false) {
    if (refresh)
      println("Warning: Ignoring notification. Notifications not supported (yet)")
    relationships = (src, dst) :: relationships
  }

  def findResources(ref: ResourceRefV): List[Resource] =
    resources.filter(PuppetCompile.evalResourceRef(ref)(_))

  private def flattenedGraph(g: Graph[Node, DiEdge]): Graph[Node, DiEdge] = {
    val restypes = g.nodes.filter(x => x.value.isInstanceOf[Resource]).map(_.value)
    var edges = g.edges.filter(e => e._1.isInstanceOf[Resource] && e._2.isInstanceOf[Resource]).map (e => e._1.value ~> e._2.value)
    val _edges = g.nodes map ({ case cl:HostClass =>
      for (from <- cl.inNeighbors;
           to <- cl.outNeighbors) yield from.value ~> to.value
    })

    edges = edges ++ _edges.flatten

    Graph.from(restypes, edges)
  }

  def toGraph (): Graph[Node, DiEdge] = {
    val _edges = relationships.map({ case(fltr1, fltr2) =>
      for(source <- findResources(fltr1).asInstanceOf[List[Node]];
          target <- findResources(fltr2).asInstanceOf[List[Node]])
        yield source ~> target
    })

    var edges = _edges.flatten
    val class_edges = containers map ({case (r, c) =>
      klasses.find(_.name == c).get.asInstanceOf[Node] ~> r.asInstanceOf[Node]})
    edges = class_edges ::: edges
    Graph.from(elements, edges)
  }

  def addHostClass (cl: HostClass) {
    klasses = cl :: klasses
  }
}
