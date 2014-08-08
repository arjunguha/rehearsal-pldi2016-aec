package puppet.core.eval

import puppet.core._
import puppet.core.eval._
import puppet.core.eval.{Attribute => Attr}
import scala.collection.{mutable => mut}
import scala.collection._

/* Functions that are callable in puppet files */
object Function {

  type ContainedBy = Option[ResourceRefV]
  type Argument = (Value, ASTCore)

  trait FunctionApp {
    protected def Value(a: Argument) = a._1
    protected def Type(a: Argument) = a._2
    def apply (catalog: Catalog,
               containedBy: ContainedBy,
               arg: Argument*): Value
  }

  // XXX : Should there be a trait/Partial Function to capture sanity checks before calling a function
  object Notice extends FunctionApp {
    override def apply (catalog: Catalog,
                        containedBy: ContainedBy,
                        arg: Argument*): Value = {
      println(Value(arg(0)).toPString)
      UndefV
    }
  }

  object Include extends FunctionApp {
    override def apply(catalog: Catalog,
                       containedBy: ContainedBy,
                       arg: Argument*): Value = { 
      arg.foreach(a => {
        // TODO : Remove asInstanceOf
        catalog.addResource(Attr.resourceBasicAttributes("Class", Value(a).asInstanceOf[StringV].value))
      })
      UndefV
    }
  }

  object Require extends FunctionApp {
    override def apply(catalog: Catalog,
                       containedBy: ContainedBy,
                       arg: Argument*): Value = {
      arg.foreach(a => {
        // TODO : Remove asInstanceOf
        val ref = catalog.addResource(Attr.resourceBasicAttributes("Class", Value(a).asInstanceOf[StringV].value))
        catalog.addRelationship(containedBy.get, ref)
      })
      UndefV
    }
  }

  object Contain extends FunctionApp {
    override def apply(catalog: Catalog,
                       containedBy: ContainedBy,
                       arg: Argument*): Value = {
      arg.foreach(a => {
        // TODO : Remove asInstanceOf
        catalog.addResource(Attr.resourceBasicAttributes("Class", Value(a).asInstanceOf[StringV].value),
                            containedBy)
      })
      UndefV
    }
  }

  object Fail extends FunctionApp {
    override def apply(catalog: Catalog,
                       containedBy: ContainedBy,
                       arg: Argument*): Value = {
      throw new Exception("Error: %s".format(Value(arg(0)).toPString))
    }
  }

  object Defined extends FunctionApp {

    private def type_exists(t: String): Boolean = 
      KnownResource.types.exists(_ == t) ||
      TypeCollection.getClass(t).isDefined ||
      TypeCollection.getDefinition(t).isDefined

    private def defined(catalog: Catalog, v: Value, t: ASTCore): Boolean =
    (v, t) match {
      case (UndefV, _: VariableC) => false
      case (_, _: VariableC) => true
      case (n: StringV, _: NameC) => type_exists(n.toPString)
      case (t: StringV, _: TypeC) => type_exists(t.toPString)
      case (ref: ResourceRefV, _) => (catalog.find(ref).length > 0)
      case _ => false
    }

    override def apply(catalog: Catalog,
                       containedBy: ContainedBy,
                       arg: Argument*): Value = {
      BoolV(arg.map((a) => defined(catalog, Value(a), Type(a))).exists(_ == true))
    }
  }

  object VersionCmp extends FunctionApp {

    import java.util.Comparator
    import java.util.Scanner

    private def compare(a: String, b: String): Int = {
      val scanner1 = new Scanner(a)
      val scanner2 = new Scanner(b)
      scanner1.useDelimiter("[\\.-]")
      scanner2.useDelimiter("[\\.-]")
      while (scanner1.hasNextInt && scanner2.hasNextInt) {
        val version1 = scanner1.nextInt;
        val version2 = scanner2.nextInt;
        if (version1 > version2) {
          return 1
        }
        else if (version1 < version2) {
          return -1
        }
      }
      if (scanner1.hasNextInt) {
          return 1
      }
      return 0
    }

    override def apply(catalog: Catalog,
                       containedBy: ContainedBy,
                       arg: Argument*): Value = {
      
      val v1 = Value(arg(0)).toPString
      val v2 = Value(arg(1)).toPString

      StringV(compare(v1, v2).toString)
    }
  }

  val fmap = Map(
    "contain" -> Contain,
    "defined" -> Defined,
    "fail"    -> Fail,
    "include" -> Include,
    "notice"  -> Notice,
    "require" -> Require,
    "versioncmp" -> VersionCmp
  )

  def apply(fname: String,
            catalog: Catalog,
            containedBy: ContainedBy,
            args: Argument*): Value = {
    val f = fmap.get(fname) getOrElse (throw new Exception(s"function: $fname not supported"))
    f(catalog, containedBy, args:_*)
  }
}
