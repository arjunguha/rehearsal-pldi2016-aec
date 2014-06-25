package puppet.core.eval

import puppet.core.eval._
import puppet.core.eval.{Attributes => Attrs}
import scala.collection.{mutable => mut}
import scala.collection._

/* Functions that are callable in puppet files */
object Function {

  type ContainedBy = Option[ResourceRefV]

  trait FunctionApp {
    def apply (catalog: Catalog,
               containedBy: ContainedBy,
               arg: Value*): Value
  }

  // XXX : Should there be a trait/Partial Function to capture sanity checks before calling a function
  object Notice extends FunctionApp {
    override def apply (catalog: Catalog,
                        containedBy: ContainedBy,
                        arg: Value*): Value = {
      println(arg(0).toPString)
      UndefV
    }
  }

  object Include extends FunctionApp {
    override def apply(catalog: Catalog,
                       containedBy: ContainedBy,
                       arg: Value*): Value = { 
      arg.foreach(v => {
        // TODO : Remove asInstanceOf
        catalog.addResource(Attrs.resourceBasicAttributes("Class", v.asInstanceOf[StringV].value))
      })
      UndefV
    }
  }

  object Require extends FunctionApp {
    override def apply(catalog: Catalog,
                       containedBy: ContainedBy,
                       arg: Value*): Value = {
      arg.foreach(v => {
        // TODO : Remove asInstanceOf
        val ref = catalog.addResource(Attrs.resourceBasicAttributes("Class", v.asInstanceOf[StringV].value))
        catalog.addRelationship(containedBy.get, ref)
      })
      UndefV
    }
  }

  object Contain extends FunctionApp {
    override def apply(catalog: Catalog,
                       containedBy: ContainedBy,
                       arg: Value*): Value = {
      arg.foreach(v => {
        // TODO : Remove asInstanceOf
        catalog.addResource(Attrs.resourceBasicAttributes("Class", v.asInstanceOf[StringV].value),
                            containedBy)
      })
      UndefV
    }
  }

  val fmap = Map("notice"  -> Notice,
                 "include" -> Include,
                 "require" -> Require,
                 "contain" -> Contain)

  def apply(fname: String,
            catalog: Catalog,
            containedBy: ContainedBy,
            args: Value*): Value = {
    (fmap(fname))(catalog, containedBy, args:_*)
  }
}
