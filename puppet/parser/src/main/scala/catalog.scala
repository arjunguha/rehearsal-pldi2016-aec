package puppet.core.eval

import puppet.core._
import scalax.collection.Graph
import scalax.collection.GraphEdge._
import scalax.collection.GraphPredef._

import scala.collection.{mutable => mut}

object KnownResource {
  val types = List("Augeas", "Computer", "Cron", "Exec",
    "File", "Filebucket", "Group", "Host", "Interface", "K5login",
    "Macauthorization", "Mailalias", "Maillist", "Mcx", "Mount",
    "Nagios_command", "Nagios_contact", "Nagios_contactgroup", "Nagios_host",
    "Nagios_hostdependency", "Nagios_hostescalation", "Nagios_hostextinfo",
    "Nagios_hostgroup", "Nagios_service", "Nagios_servicedependency",
    "Nagios_serviceescalation", "Nagios_serviceextinfo", "Nagios_servicegroup",
    "Nagios_timeperiod", "Notify", "Package", "Resources", "Router", "Schedule",
    "Scheduled_task", "Setboolean", "Selmodule", "Service", "Ssh_authorized_key",
    "Sshkey", "Stage", "Tidy", "User", "Vlan", "Yumrepo", "Zfs", "Zone", "Zpool")
}

object Params {
  type t = mut.Map[String, Value]
}

sealed abstract class CatalogElement(val params: Params.t) {
  val title = params("type").toPString + ":" + params("title").toPString
  val name  = params("title").toPString
  val stage = params.get("stage").map(_.toPString) getOrElse 'main.toString

  val sources: List[ResourceRefV] = attrToResRefs("require"):::attrToResRefs("subscribe")
  val targets: List[ResourceRefV] = attrToResRefs("before"):::attrToResRefs ("notify")

  private def depsToResRefs(v: Value): List[ResourceRefV] = v match {
    case v: ASTArrayV => v.value.toList flatMap depsToResRefs
    case v: ResourceRefV => List(v)
    case _ => throw new Exception("Value is not a valid resource reference")
  }

  private def attrToResRefs(key: String): List[ResourceRefV] =
    (params.get(key) map depsToResRefs) getOrElse List ()

  def toResourceRefV: ResourceRefV =
    ResourceRefV (ResourceRefV(StringV("type"), params ("type"), FEqOp),
                  ResourceRefV(StringV("title"), params ("title"), FEqOp), FAndOp)

  def mergeAttr (name: String, value: Value, append: Boolean = false) {
    // TODO: Maybe sanitize on name as title, name, type, namevar may not be overridable
    if (append) throw new Exception ("Append not supported yet")
    params += (name -> value)
  }
}

case class Resource(override val params: Params.t) extends CatalogElement(params)
case class HostClass(override val params: Params.t) extends CatalogElement(params)
case class Definition(override val params: Params.t) extends CatalogElement(params)

object CatalogElementFactory {
  def apply (params: Params.t): CatalogElement = {
    params("type").toPString match {
      case "Class" => HostClass(params)
      case x if KnownResource.types.contains(x) => Resource(params)
      case _ => Definition(params)
    }
  }
}

class Catalog {
  type Node = eval.CatalogElement
  type Filter = ResourceRefV
  type Override = (Filter, Params.t)

  var elements  = List[Node]()
  var klasses = List[HostClass]()
  var defines = List[Definition]()
  var overrides = List[Override]()
  var relationships = List[(ResourceRefV, ResourceRefV)]()

  private def isDuplicate(e: CatalogElement): Boolean =
    elements.exists(_.title == e.title)

  def addResource(params: Params.t, containedBy: Option[ResourceRefV] = None): ResourceRefV = {
    val elem = CatalogElementFactory(params)

    // TODO : Should ignore duplicate class
    if (isDuplicate(elem)) throw new Exception("Resource %s already exists in catalog".format(elem.title))
    elements = elem :: elements
    elem match {
      case r: Resource => ()
      case h: HostClass => klasses = h :: klasses
      case d: Definition => defines = d :: defines
    }

    containedBy.map(addRelationship(_, elem.toResourceRefV))
    elem.sources.foreach(addRelationship(_, elem.toResourceRefV))
    elem.targets.foreach(addRelationship(elem.toResourceRefV, _))

    elem.toResourceRefV
  }

  def addOverride (filter: Filter, attrs: Params.t) {
    // Duplicates are ok as long as merge is idempotent, which it is not due to append, but again append is not supported yet
    overrides = (filter, attrs) :: overrides
  }

  def addRelationship(src: ResourceRefV, dst: ResourceRefV, refresh: Boolean = false) {
    if (refresh)
      println("Warning: Ignoring notification. Notifications not supported (yet)")

    relationships = (src, dst) :: relationships
  }
  
  def find(ref: ResourceRefV): List[Node] =
    elements.filter(PuppetCompile.evalResourceRef(ref)(_))

  // Grab a "class" node and form a cross product of incoming edges with outgoing edges for a flattened graph
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
    val edges = relationships.map({ case(fltr1, fltr2) =>
      for(source <- find(fltr1)/*.asInstanceOf[List[Node]]*/;
          target <- find(fltr2)/*.asInstanceOf[List[Node]]*/)
        yield source ~> target
    })

    Graph.from(elements, edges.flatten)
  }

  def getNextClass(): Option[HostClass] = klasses match {
    case Nil => None
    case hd :: tl => klasses = tl; Some(hd)
  }

  def getNextDefinition(): Option[Definition] = defines match {
    case Nil => None
    case hd :: tl => defines = tl; Some(hd)
  }
}
