package puppet.core.eval

import puppet.core.eval._

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
                         /*
      arg.foreach(v => {
        val name = v.asInstanceOf[StringV].value
        catalog.addClass(name,
                         List("type"->StringV("Class"),
                              "title"->StringV(name)))
      })
      */
      UndefV
    }
  }

  object Require extends FunctionApp {
    override def apply(catalog: Catalog,
                       containedBy: ContainedBy,
                       arg: Value*): Value = {
                         /*
      arg.foreach(v => {
        val name = v.asInstanceOf[StringV].value
        catalog.addClass(name,
                         List("type"->StringV("Class"),
                              "title"->StringV(name)))
        catalog.addClassRelationship()
      })
      */

      UndefV
    }
  }

  object Contain extends FunctionApp {
    override def apply(catalog: Catalog,
                       containedBy: ContainedBy,
                       arg: Value*): Value = {
                         /*
      arg.foreach(v => {
        val name = v.asInstanceOf[StringV].value
        catalog.addClass(name,
                         List("type"->StringV("Class"),
                              "title"->StringV(name)))
        catalog.addClassRelationship()
      })
      */
      UndefV
    }
  }

  import scala.collection._

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
