package puppet.common.resource

import scala.collection.Map

sealed abstract trait Value
case object UndefV extends Value
case class BoolV(value: Boolean) extends Value
case class StringV(value: String) extends Value
case class ASTHashV(value: Map[String, Value]) extends Value
case class ASTArrayV(value: Array[Value]) extends Value

case class Resource(attrs: Map[String, Value]) extends Serializable {
  val typ = attrs("type").asInstanceOf[StringV].value
  val name = attrs("name").asInstanceOf[StringV].value.stripPrefix("::")
  val title = typ + ":" + name
}
