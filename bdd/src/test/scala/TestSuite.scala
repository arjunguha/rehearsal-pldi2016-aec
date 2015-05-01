import bdd.Bdd

class TestSuite extends org.scalatest.FunSuite {

  test("ff") {

    val bdd = Bdd[String]((x, y) => x < y)
    val bdd2 = Bdd[String]((x, y) => x < y)
    import bdd._
    import Implicits._

    val x = bddTrue && bddFalse
    assert(x == bddFalse)
    info(x.toString)


  }


}