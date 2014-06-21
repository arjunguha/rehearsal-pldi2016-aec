package puppet.core.eval

/* Functions that are callable in puppet files */
object Function {

  type Parent = String

  trait FunctionApp {
    def apply (catalog: Catalog,
               parent: Parent,
               arg: Value*): Value
  }

  // XXX : Should there be a trait/Partial Function to capture sanity checks before calling a function
  object Notice extends FunctionApp {
    override def apply (catalog: Catalog,
                        parent: Parent,
                        arg: Value*): Value = {
      println(arg(0).toPString)
      UndefV
    }
  }

  object Include extends FunctionApp {
    override def apply(catalog: Catalog,
                       parent: Parent,
                       arg: Value*): Value = { 
      // XXX: eval immediately 
      arg.foreach(v => {
        val name = v.asInstanceOf[StringV].value
        catalog.addClass(name,
                         List("type"->StringV("Class"),"title"->StringV(name)),
                         parent)
      })
      UndefV
    }
  }

  object Require extends FunctionApp {
    override def apply(catalog: Catalog,
                       parent: Parent,
                       arg: Value*): Value = {
      throw new Exception("Require function not Supported yet")
      UndefV
    }
  }

  object Contain extends FunctionApp {
    override def apply(catalog: Catalog,
                       parent: Parent,
                       arg: Value*): Value = {
      throw new Exception("Contain function not Supported yet")
      UndefV
    }
  }

  import scala.collection._

  val fmap = Map ("notice"  -> Notice,
                  "include" -> Include,
                  "require" -> Require,
                  "contain" -> Contain)

  def apply(fname: String,
            catalog: Catalog,
            parent: Parent,
            args: Value*): Value = {
    (fmap(fname))(catalog, parent, args:_*)
  }
}
