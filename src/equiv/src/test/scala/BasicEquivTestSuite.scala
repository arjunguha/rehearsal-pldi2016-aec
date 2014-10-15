import equiv.ast._

import org.scalatest.{FunSuite, Matchers}

class Core extends FunSuite with Matchers {
  import z3.scala._
  import z3.scala.dsl._

  import equiv.sat._

  val z3p = new Z3Puppet()

  test("sanity check") {
    // Should get unknown or sat
    z3p.printAssertions
    assert(Some(false) != z3p.sanityCheck())
  }

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

  test("Group creation should commute for different groups") {

    import equiv.semantics._
    import puppet.common.resource._

    val attrs1 = Map("type" -> StringV("Group"),
                     "name" -> StringV("abc"),
                     "ensure" -> StringV("present"),
                     "managehome" -> StringV("yes"))
    val attrs2 = Map("type" -> StringV("Group"),
                     "name" -> StringV("xyz"),
                     "ensure" -> StringV("present"),
                     "managehome" -> StringV("yes"))

    val u1 = Provider(Resource(attrs1))
    val u2 = Provider(Resource(attrs2))
    assert(Some(true) == z3p.isEquiv(u1.toFSOps, u2.toFSOps))
  }


  /*
  test("user creation should commute for different users") {

    import equiv.semantics._
    import puppet.common.resource._

    val attrs1 = Map("type" -> StringV("User"),
                     "name" -> StringV("abc"),
                     "ensure" -> StringV("present"),
                     "managehome" -> StringV("yes"))
    val attrs2 = Map("type" -> StringV("User"),
                     "name" -> StringV("xyz"),
                     "ensure" -> StringV("present"),
                     "managehome" -> StringV("yes"))

    val u1 = Provider(Resource(attrs1))
    val u2 = Provider(Resource(attrs2))
    assert(Some(true) == z3p.isEquiv(u1.toFSOps, u2.toFSOps))
  }
  */

  /*
  // This test hangs
  test("creating two distinct paths is not the same") {
     assert(Some(true) == z3p.isEquiv(MkDir("/a"), MkDir("/b")))
  }

  test ("creating two distinct paths is not the same 2") {

    import z3p._ 

    val p1 = z3p.toZ3Path("/a")
    val p2 = z3p.toZ3Path("/b")

    val axiom = mkdir(p1) === mkdir(p2)
    assert(Some(false) == z3p.isSatisfiable(axiom))
  }
  */
}
