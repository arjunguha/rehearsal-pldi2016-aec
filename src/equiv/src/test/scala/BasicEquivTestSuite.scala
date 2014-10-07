import equiv.ast._

import org.scalatest.{FunSuite, Matchers}

class Core extends FunSuite with Matchers {
  import z3.scala._
  import z3.scala.dsl._

  import equiv.sat._

  val z3p = new Z3Puppet()

  test("mkdir commutes") {
    val e1 = Block(MkDir("/a"), MkDir("/b"))
    val e2 = Block(MkDir("/b"), MkDir("/a"))
    assert(Some(true) == z3p.isEquiv(e1, e2))
  }

  test("mkdir commutes (2x associativity needed)") {
    val e1 = Block(MkDir("/a"), Block(MkDir("/b"), MkDir("/c")))
    val e2 = Block(Block(MkDir("/c"), MkDir("/a")), MkDir("/b"))
    assert(Some(true) == z3p.isEquiv(e1, e2))
  }

  test("mkdir commutes (3x associativity needed)") {
    val e1 = Block(MkDir("/a"), Block(MkDir("/c"), MkDir("/b")))
    val e2 = Block(Block(MkDir("/c"), MkDir("/a")), MkDir("/b"))
    assert(Some(true) == z3p.isEquiv(e1, e2))
  }

  // This test hangs
  // test("creating two distinct paths is not the same") {
  //   assert(Some(true) == z3p.isEquiv(MkDir("/a"), MkDir("/b")))
  // }


}
