import bdd.Bdd

class TestSuite extends org.scalatest.FunSuite {

  test("basic bdd usage") {
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


}
