package puppet.core.eval

import puppet.core._
import scala.collection.{mutable => mut}

sealed abstract class CatalogElement(params: mut.Map[String, Value]) {
  val title = params("type").toPString + ":" + params("title").toPString
  val name  = params("title").toPString
  // val stage = params.get("stage").map(_toPString) getOrElse 'main.toString

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

case class Resource(params: mut.Map[String, Value]) extends CatalogElement(params)
case class HostClass(params: mut.Map[String, Value]) extends CatalogElement(params)
case class Stage(params: mut.Map[String, Value]) extends CatalogElement(params)
