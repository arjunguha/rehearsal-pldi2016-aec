package puppet.core.eval

import puppet.core._
import puppet.{core => core}
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

case class Attribute(name: String, value: Value)

object Attribute {

  private def nameAttribute(value: Value): Attribute = Attribute("name", value)
  private def namevarAttribute(value: Value): Attribute = Attribute("namevar", value)
  private def typeAttribute(value: Value): Attribute = Attribute("type", value)

  def resourceBasicAttributes(typ: String, name: String): List[Attribute] = {
    List(nameAttribute(StringV(name)),
         namevarAttribute(StringV(name)),
         typeAttribute(StringV(typ.capitalize)))
  }
}

sealed abstract class CatalogElement(attrs: List[Attribute]) {
  val params = mut.Map(attrs.map((a) => (a.name, a.value)).toSeq:_*)
  val typ   = params("type").toPString
  val name  = params("name").toPString.stripPrefix("::")
  val title = typ + ":" + name
  // XXX: Maybe stage should be deferred until later (override can give it a value at a later stage)
  //      Default stage value should rather be employed by catalog/compiler and not here.
  // val stage = params.get("stage").map(_.toPString) getOrElse 'main.toString

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

  def overwriteAttribute (name: String, value: Value) {
    params += (name -> value)
  }

  def addAttribute (name: String, value: Value) {
    if (params.get(name).isDefined)
      throw new Exception(s"Attribute $name already defined for element: $title")
    else 
      params += (name -> value)
  }

  def appendAttribute (name: String, value: Value) {
    val oval = params.get(name)
    if (oval.isDefined) {
      (oval.get, value) match {
        case (UndefV, _) => params += (name -> value)
        case (x: BoolV, y: BoolV) => params += (name -> ASTArrayV(Array(x, y)))
        case (x: BoolV, y: StringV) => params += (name -> ASTArrayV(Array(x, y)))
        case (x: StringV, y: BoolV) => params += (name -> ASTArrayV(Array(x, y)))
        case (x: StringV, y: StringV) => params += (name -> ASTArrayV(Array(x, y)))
        case (x: ASTArrayV, y: ASTArrayV) => params += (name -> x.append(y))
        case (x: ASTArrayV, y: BoolV) => params += (name -> x.append(ASTArrayV(Array(y))))
        case (x: ASTArrayV, y: StringV) => params += (name -> x.append(ASTArrayV(Array(y))))
        case (x: BoolV, y: ASTArrayV) => params += (name -> ASTArrayV(Array(x)).append(y))
        case (x: StringV, y: ASTArrayV) => params += (name -> ASTArrayV(Array(x)).append(y))
        case _ => throw new Exception("Didn't anticipate append of this type of attributes")
      }
    }
    else
      params += (name -> value)
  }

  def attributeExists(name: String): Boolean =
    params.get(name).isDefined

  override def toString = title
}

case class Resource(as: List[Attribute]) extends CatalogElement(as) {
  override def toString = title

  /*
   * Omits complex attributes and turns other attributes to string
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

case class HostClass(as: List[Attribute]) extends CatalogElement(as)
case class Definition(as: List[Attribute]) extends CatalogElement(as)

sealed abstract class AttributeOverride(name: String, value: Value)
case class AppendAttribute(name: String, value: Value) extends AttributeOverride(name: String, value: Value)
case class ReplaceAttribute(name: String, value: Value) extends AttributeOverride(name: String, value: Value)


object CatalogElement {
  def apply (params: List[Attribute]): CatalogElement = {
    params.find(_.name == "type").get.value.toPString match {
      case "Class" => HostClass(params)
      case x if KnownResource.types.contains(x) => Resource(params)
      case _ => Definition(params)
    }
  }
}

sealed abstract class Override(val filter: ResourceRefV, val attrs: List[AttributeOverride]) {
  def query: ResourceRefV = filter
}

case class ReferenceOverride(f: ResourceRefV,
                             as: List[AttributeOverride],
                             scope: String) extends Override(f, as) {
  override def query: ResourceRefV =  {
    val scopefilter = ResourceRefV(StringV("scopetag"), StringV(scope), FEqOp)
    ResourceRefV(scopefilter, filter, FAndOp)
  }
}

case class CollectionOverride(f: ResourceRefV,
                              as: List[AttributeOverride]) extends Override(f, as)

case class DefaultsOverride(f: ResourceRefV,
                            as: List[AttributeOverride],
                            scope: String) extends Override(f, as) {
  override def query: ResourceRefV = {
    val scopefilter = ResourceRefV(StringV("scopetag"), StringV(scope), FEqOp)
    ResourceRefV(scopefilter, filter, FAndOp)
  }
}

object Override {
  def apply(filter: ResourceRefV,
            attrs: List[AttributeOverride],
            kind: core.Override,
            scope: String): Override = kind match {
    case core.ReferenceOverride => ReferenceOverride(filter, attrs, scope)
    case core.CollectionOverride => CollectionOverride(filter, attrs)
    case core.DefaultsOverride => DefaultsOverride(filter, attrs, scope)
  }
}

class Catalog {
  type Filter = ResourceRefV

  var resources = List[Resource]()
  var klasses = List[HostClass]()
  var defines = List[Definition]()
  var overrides = List[Override]()
  var relationships = List[(ResourceRefV, ResourceRefV)]()

  var containment = mut.Map[ResourceRefV, Set[ResourceRefV]]()
  private def getContainedElements(containedBy: ResourceRefV): Set[ResourceRefV] =
    containment getOrElse(containedBy, Set())
    
  private def elements = (resources ::: klasses ::: defines)

  private def isDuplicate(e: CatalogElement): Boolean =
    elements.exists(_.title == e.title)

  def addResource(params: List[Attribute],
                  containedBy: Option[ResourceRefV] = None,
                  scope: Option[String] = None): ResourceRefV = {

    val elem = CatalogElement(params)
    val elemRef = elem.toResourceRefV

    (elem, isDuplicate(elem)) match {
      case (r: Resource, true) => throw new Exception("Resource %s already exists in catalog".format(elem.title))
      case (r: Resource, false) => resources = r :: resources
      case (h: HostClass, true) => () // Ignore duplicate class instantiation
      case (h: HostClass, false) => klasses = h :: klasses
      case (d: Definition, true) => throw new Exception("Definition %s already exists in catalog".format(elem.title))
      case (d: Definition, false) => defines = d :: defines
    }

    if (elem.isInstanceOf[Resource] && scope.isDefined) {
      elem.addAttribute("scopetag", StringV(scope.get))
    }

    if (containedBy.isDefined) {
      containment.put(containedBy.get,
                      getContainedElements(containedBy.get) + elemRef)
    }

    elemRef
  }

  def addOverride(ovrd: Override) = overrides = ovrd :: overrides

  def addRelationship(src: ResourceRefV, dst: ResourceRefV, refresh: Boolean = false) {
    if (refresh)
      println("Warning: Ignoring notification. Notifications not supported (yet)")

    relationships = (src, dst) :: relationships
  }

  private def findFirst(ref: ResourceRefV): CatalogElement =
    elements.filter(PuppetCompile.evalResourceRef(ref)(_)).head

  private def getContainedResources(container: CatalogElement): List[Resource] = container match {
    case r: Resource => List(r)
    case _ => getContainedElements(container.toResourceRefV)
               .map(c => getContainedResources(findFirst(c))).toList.flatten
  }

  def find(ref: ResourceRefV): List[CatalogElement] =
    elements.filter(PuppetCompile.evalResourceRef(ref)(_))
    
  private def findResources(ref: ResourceRefV): List[Resource] =
    find(ref).map(getContainedResources(_)).flatten

  def resourceCount: Int = resources.length

  def toGraph (): Graph[Resource, DiEdge] = {
    val edges = relationships.map({ case(fltr1, fltr2) =>
      for(source <- findResources(fltr1);
          target <- findResources(fltr2))
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
