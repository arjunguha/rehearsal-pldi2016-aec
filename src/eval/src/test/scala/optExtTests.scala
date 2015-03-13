import fsmodel.optExt._
import fsmodel.optExt.Implicits._
import fsmodel.core.Implicits._

class OptExtTests extends org.scalatest.FunSuite {
  val a = Mkdir("/a")
  val b = Mkdir("/b")
  val c = Mkdir("/c")

  test("single star") {
    val e = a * b
    // info(e.unconcur.pretty)
    info(e.unconcurOpt.pretty)
  }

  test(">> * atomic") {
    val e = (a >> b) * c
    // info(e.unconcur.pretty)
    info(e.unconcurOpt.pretty)
  }

  test("nested stars") {
    val e = (a * b) * c
    // info(e.unconcur.pretty)
    info(e.unconcurOpt.pretty)
  }

  test("alt") {
    val e = (a + b) * c
    // info(e.unconcur.pretty)
    info(e.unconcurOpt.pretty)
  }

  test("Error in sequence") {
    val e = Error >> a >> b >> Error >> c
    info(e.unconcurOpt.pretty)
  }

}
