package puppet.core.eval

/* Functions that are callable in puppet files */
object Function {

  type Parent = HostClass

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
      println (arg (0).asInstanceOf[StringV].value)
      UndefV
    }
  }

  object Include extends FunctionApp {
    override def apply (catalog: Catalog,
                        parent: Parent,
                        arg: Value*): Value = { 
      arg.foreach ({ case v: Value => 
        catalog.addClass (v.asInstanceOf[StringV].value, List ())
      })
      UndefV
    }
  }

  object Require extends FunctionApp {
    override def apply (catalog: Catalog, 
                        parent: Parent,
                        arg: Value*): Value = {
      throw new Exception ("Require function not Supported yet")
      UndefV
    }
  }

  object Contain extends FunctionApp {
    override def apply (catalog: Catalog,
                        parent: Parent,
                        arg: Value*): Value = {
      throw new Exception ("Contain function not Supported yet")
      UndefV
    }
  }

  import scala.collection._

  val fmap = Map ("notice"  -> Notice,
                  "include" -> Include,
                  "require" -> Require,
                  "contain" -> Contain)

  def apply (fname: String,
             catalog: Catalog,
             parent: Parent,
             args: Value*): Value = {
    (fmap (fname)) apply (catalog, parent, args:_*)
  }
}
