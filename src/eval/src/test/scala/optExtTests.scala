import fsmodel.optExt._
import fsmodel.optExt.Implicits._
import fsmodel.core.Implicits._

class OptExtTests extends org.scalatest.FunSuite {

  test("scratch") {
    val e = Mkdir("/a") * Mkdir("/b")
    info(e.unconcur.pretty)
    // info(e.unconcurOpt.pretty)
  }

  test(">> * atomic") {
    val e = (Mkdir("/a") >> Mkdir("/b")) * Mkdir("/c")
    info(e.unconcur.pretty)
    // info(e.unconcurOpt.pretty)
  }

}
