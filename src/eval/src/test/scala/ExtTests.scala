import eval._
import eval.Implicits._

class ExtTests extends org.scalatest.FunSuite {

  // TODO(arjun): I'm not sure how to properly test unconcur
  test("atomic * atomic") {
    val e = Mkdir("/a") * Mkdir("/b")
    info(e.unconcur.pretty)
    info(e.unconcurOpt.pretty)
  }

  test(">> * atomic") {
    val e = (Mkdir("/a") >> Mkdir("/b")) * Mkdir("/c")
    info(e.unconcur.pretty)
    info(e.unconcurOpt.pretty)
  }

  test("nested stars") {
    val e = (Mkdir("/a") * Mkdir("/b")) * Mkdir("/c")
    info(e.unconcur.pretty)
    info(e.unconcurOpt.pretty)
  }

}
