package puppet.common.resource

import scala.collection.Map

sealed abstract trait Value
case object UndefV extends Value
case class BoolV(value: Boolean) extends Value
case class StringV(value: String) extends Value
case class ArrayV(value: Array[Value]) extends Value

trait Extractor[T] { def extract(from: Value): Option[T] }

object Extractor {

  implicit def stringExtractor: Extractor[String] =
    new Extractor[String] { def extract(from: Value): Option[String] = from match {
      case StringV(str) => Some(str)
      case _ => None
    }}

  implicit def boolExtractor: Extractor[Boolean] =
    new Extractor[Boolean] { def extract(from: Value): Option[Boolean] = from match {
      case BoolV(b) => Some(b)
      case _ => None
    }}

  implicit def arrayExtractor: Extractor[Array[Value]] =
    new Extractor[Array[Value]] { def extract(from: Value): Option[Array[Value]] = from match {
      case ArrayV(arr) => Some(arr)
      case _ => None
    }}
}

case class Resource(attrs: Map[String, Value]) {
  val typ = attrs("type").asInstanceOf[StringV].value
  val name = attrs("name").asInstanceOf[StringV].value.stripPrefix("::")
  val title = typ + ":" + name

  def get[T](k: String)(implicit ex: Extractor[T]): Option[T] =
    attrs.get(k).flatMap((v) => ex.extract(v))

  def getRawVal(k: String): Option[Value] = attrs.get(k)
}
