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

object Attributes {
  type T = mut.Map[String, Value]

  def resourceBasicAttributes(typ: String, name: String): T = {
    mut.Map("type"->StringV(typ.capitalize),
            "name"->StringV(name),
            "namevar"->StringV(name))
  }
}

sealed abstract class CatalogElement(val params: Attributes.T) {
  val typ   = params("type").toPString
  val name  = params("name").toPString
  val title = typ + ":" + name
  // XXX: Maybe stage should be deferred until later (override can give it a value at a later stage)
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
                  ResourceRefV(StringV("name"), params ("name"), FEqOp), FAndOp)

  def mergeAttr (name: String, value: Value, append: Boolean = false) {
    // TODO: Maybe sanitize on name as title, name, type, namevar may not be overridable
    if (append) throw new Exception ("Append not supported yet")
    params += (name -> value)
  }

  override def toString = title
}

case class Resource(override val params: Attributes.T) extends CatalogElement(params) {
  override def toString = title

  /*
   * Omits complex attributes and turns the other attributes to string
   * If an attribute has a value of type Array, only the first element of 
   * array is preserved
   */
  def toStringAttributes: Map[String, String] = {
    params.filter({case (k, _) => !(k == "require" || k == "before" || k == "notify" || k == "subscribe") })
          .collect({ case (k, v: BoolV) => (k, v.toPString)
                     case (k, v: StringV) => (k, v.toPString)
                   }).toMap
  }
}

case class HostClass(override val params: Attributes.T) extends CatalogElement(params)
case class Definition(override val params: Attributes.T) extends CatalogElement(params)

object CatalogElement {
  def apply (params: Attributes.T): CatalogElement = {
    params("type").toPString match {
      case "Class" => HostClass(params)
      case x if KnownResource.types.contains(x) => Resource(params)
      case _ => Definition(params)
    }
  }
}

class Catalog {
  type Filter = ResourceRefV
  type Override = (Filter, Attributes.T)

  var elements  = List[CatalogElement]()
  var klasses = List[HostClass]()
  var defines = List[Definition]()
  var overrides = List[Override]()
  var relationships = List[(ResourceRefV, ResourceRefV)]()

  var containment = mut.Map[ResourceRefV, Set[ResourceRefV]]()

  private def isDuplicate(e: CatalogElement): Boolean =
    elements.exists(_.title == e.title)

  def addResource(params: Attributes.T, containedBy: Option[ResourceRefV] = None): ResourceRefV = {

    val elem = CatalogElement(params)
    val elemRef = elem.toResourceRefV

    (elem, isDuplicate(elem)) match {
      case (r: Resource, true) => throw new Exception("Resource %s already exists in catalog".format(elem.title))
      case (r: Resource, false) => ()
      case (h: HostClass, true) => ()
      case (h: HostClass, false) => klasses = h :: klasses
      case (d: Definition, true) => throw new Exception("Definition %s already exists in catalog".format(elem.title))
      case (d: Definition, false) => defines = d :: defines
    }

    if (!containedBy.isEmpty) {
      val refs = containment getOrElse(containedBy.get, Set[ResourceRefV]())
      containment.put(containedBy.get, refs + elemRef)
    }

    elem.sources.foreach(addRelationship(_, elemRef))
    elem.targets.foreach(addRelationship(elemRef, _))

    elements = elem :: elements

    elemRef
  }

  def addOverride (filter: Filter, attrs: Attributes.T) =
    overrides = (filter, attrs) :: overrides

  def addRelationship(src: ResourceRefV, dst: ResourceRefV, refresh: Boolean = false) {
    if (refresh)
      println("Warning: Ignoring notification. Notifications not supported (yet)")

    relationships = (src, dst) :: relationships
  }

  private def findFirst(ref: ResourceRefV): CatalogElement =
    elements.filter(PuppetCompile.evalResourceRef(ref)(_)).head

  private def containedResources(elem: CatalogElement): List[Resource] = elem match {
    case r: Resource => List(r)
    case _ => ((containment getOrElse (elem.toResourceRefV, Set[ResourceRefV]()))
               .map(e => containedResources(findFirst(e)))).toList.flatten
  }

  def find(ref: ResourceRefV): List[CatalogElement] =
    elements.filter(PuppetCompile.evalResourceRef(ref)(_))

  def resourceCount: Int = resources.length
  def resources: List[Resource] = elements.collect({ case r: Resource => r})

  // Produces a flattened graph consisting only of Resources
  def toGraph (): Graph[Resource, DiEdge] = {
    val edges = relationships.map({ case(fltr1, fltr2) =>
      for(source <- find(fltr1).map(containedResources(_)).flatten;
          target <- find(fltr2).map(containedResources(_)).flatten)
        yield source ~> target
    })

    // println ("#Resources: " + resourceCount.toString)
    Graph.from(resources, edges.flatten)
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
