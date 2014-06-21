package puppet.core.eval

import scala.util.matching.Regex

// TODO : common 'value' parameter and its type
sealed abstract trait Value {

  /* Puppets idiosyncracies on what can be (automatically) coerced
   * into what type
   */
  def toBool: Boolean   = throw new Exception("Incompatible type for conversion to bool")
  def toInt: Int        = throw new Exception("Incompatible type for conversion to Int")
  def toDouble: Double  = throw new Exception("Incompatible type for conversion to Double")
  def toPString: String = throw new Exception("Incompatible type for conversion to String")
  def isEqual (other: Value): Boolean = false
   
  type T <: Value
  type U <: Value
  def append (other: T): U = throw new Exception("Incompatible type for appending")
}

case object UndefV extends Value {
  override def toBool = false
  override def toPString = ""
}

case class BoolV (value: Boolean) extends Value {
  override def toBool = value
  override def toPString = value.toString
  override def isEqual (other: Value): Boolean =
    other.isInstanceOf[BoolV] && other.asInstanceOf[BoolV].value == value
}

case class StringV (value: String) extends Value {
  override def toBool = 
    ! (value == "" || value == "\"\"" || value == "''") // Empty strings, quoted or otherwise are false
  override def toDouble = value.toDouble
  // First try to parse Octal, if it fails then hex then decimal
  override def toInt = value.toInt // TODO : Add support for hex and octal
  override def toPString = value
  override def isEqual (other: Value): Boolean =
    // this is a case insensitive equality
    other.isInstanceOf[StringV] && 
    other.asInstanceOf[StringV].value.toLowerCase == value.toLowerCase

  type T = Value
  type U = StringV
  override def append (other: T): U = StringV (value + other.toPString)
}

case class RegexV (value: Regex) extends Value {
  override def toPString = value.toString
}

object PuppetCompositeValueTypes {
  type ValueHashMap = Map[String, Value]
  type ValueArray   = Array[Value]
  type ValueRef     = Map[String, Value]
}

import PuppetCompositeValueTypes._

case class ASTHashV (value: Map[String, Value]) extends Value {
  override def toBool = true // Empty hashes are coerced to true as well
  override def toPString = 
    value.foldLeft("")((acc, e) => acc + e._1 + e._2.toPString)
  override def isEqual (other: Value): Boolean =
    other.isInstanceOf[ASTHashV] &&
    other.asInstanceOf[ASTHashV].value.size == value.size &&
    other.asInstanceOf[ASTHashV].value.forall ({ case (k, v) => 
      (value contains k) && value(k).isEqual(v)
    })

  type T = ASTHashV
  type U = ASTHashV
  override def append (other: T): U = ASTHashV ((value.toList ::: other.value.toList).toMap)
}

case class ASTArrayV (value: ValueArray) extends Value {
  override def toBool = true // Even empty arrays are coerced to true
  override def toPString = value.foldLeft ("") (_ + _.toPString)
  override def isEqual (other: Value): Boolean = 
    other.isInstanceOf[ASTArrayV] &&
    other.asInstanceOf[ASTArrayV].value.size == value.size &&
    ((for (i <- value.indices 
           if ! value (i).isEqual (other.asInstanceOf[ASTArrayV].value (i))) yield false).length  == 0)

  type T = ASTArrayV
  type U = ASTArrayV
  override def append (other: T): U = ASTArrayV (value ++ other.value)
}

case class ResourceRefV (lhs: Value, rhs: Value, op: puppet.core.FilterOp) extends Value {
  override def toBool = true /* any resource reference is true */
  /*
  override def toPString = "%s[%s]". format (value._1.captialize,
                                             value._2 mkString ", ")
  */
}
