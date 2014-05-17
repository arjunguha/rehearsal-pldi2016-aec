package puppet.core.eval

/* Functions that are callable in puppet files */
object Function {

  // XXX : Should there be a trait/Partial Function to capture sanity checks before calling a function


  object Notice {
    def apply (arg: Value*): Value = { println (arg (0).asInstanceOf[StringV].value); UndefV }
  }

  import scala.collection._

  val fmap = Map ("notice" -> Notice)

  def apply (fname: String, args: Value*): Value = {
    (fmap (fname)) apply (args:_*)
  }
}
