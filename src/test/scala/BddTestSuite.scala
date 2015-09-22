import bdd.Bdd

class TestSuite extends org.scalatest.FunSuite {

  def testBdd(label: String)(f: Bdd[String] => Unit): Unit = {
    test(label) {
      f(Bdd[String]((x, y) => x < y))
    }
  }

  test("basic bdd creation") {
    val bdd = Bdd[String]((x, y) => x < y)
    import bdd._
    import Implicits._

    val x = bddTrue && bddFalse
    assert(x == bddFalse)

    val y = bddVar("foo") || bddFalse
    assert(y == bddVar("foo"))

    val z = bddVar("a") && (bddVar("b") || bddVar("c")) && bddTrue
    assert(z == (bddVar("a") && (bddVar("b") || bddVar("c"))))
  }

  testBdd("var and false") { bdd =>
    import bdd._
    import Implicits._
    assert ((bddVar("a") && bddFalse) == bddFalse)
  }

  test("bddRestrict tests") {
    val bdd = Bdd[String]((x, y) => x < y)
    import bdd._
    import Implicits._

    assert(bddRestrict(bddVar("a") && bddVar("b"), "a", false) == bddFalse)
    assert(bddRestrict(bddVar("a") || bddVar("b"), "b", true) == bddTrue)
    val x = bddVar("a") && bddVar("b") && bddVar("c")
    assert(bddRestrictAll(x, List(("a", true), ("b", true))) == bddVar("c"))
    assert(bddRestrictAll(x, List(("a", false), ("b", true))) == bddFalse)
  }

  test("bddFold") {
    val bdd = Bdd[String]((x, y) => x < y)
    import bdd._
    import Implicits._
    assert(bddFold("", "")(bddVar("a") && bddVar("b") || bddVar("c"), (a, b, c) => b + a + c) ==
           "acbc")
  }

}
