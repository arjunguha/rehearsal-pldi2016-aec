import fsmodel.ext._
import fsmodel.core.Implicits._

class ExtTests extends org.scalatest.FunSuite {

  // TODO(arjun): I'm not sure how to properly test unconcur
  test("atomic * atomic") {
    val e = Mkdir("/a") * Mkdir("/b")
    println(e.unconcur.pretty)
  }

  test(">> * atomic") {
    val e = (Mkdir("/a") >> Mkdir("/b")) * Mkdir("/c")
    println(e.unconcur.pretty)
  }

  test("nested stars") {
    val e = (Mkdir("/a") * Mkdir("/b")) * Mkdir("/c")
    println(e.unconcur.pretty)
  }

}
