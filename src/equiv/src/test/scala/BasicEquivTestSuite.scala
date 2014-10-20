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

  test("group test case - reduced 1") {




    val a1 = Block(Filter(equiv.ast.Not(Exists("/etc/groups/abc"))),
                   MkDir("/etc/groups/abc"),
                   CreateFile("/etc/groups/abc/settings", "bar"))
    val a2 = Filter(equiv.ast.Not(equiv.ast.Not(Exists("/etc/groups/abc"))))
    val a3 = Block(Filter(equiv.ast.Not(Exists("/etc/groups/xyz"))), MkDir("/ect/groups/xyz"),
                   CreateFile("/etc/groups/xyz/settings", "foo"))
    val a4 = Filter(equiv.ast.Not(equiv.ast.Not(Exists("/etc/groups/xyz"))))
    //val a1 =

          import equiv.semantics._
    import puppet.common.resource._

    assert(Some(true) == z3p.isEquiv(Block(a2, a4), Block(a4, a2)))
    assert(Some(true) == z3p.isEquiv(Block(a2, a3), Block(a3, a2)))
    assert(Some(true) == z3p.isEquiv(Block(a1, a3), Block(a3, a1)))
    assert(Some(true) == z3p.isEquiv(Block(a1, a4), Block(a4, a1)))
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

    val g1 = Provider(Resource(attrs1))
    val g2 = Provider(Resource(attrs2))
    assert(Some(true) == z3p.isEquiv(Block(g1.toFSOps, g2.toFSOps), Block(g2.toFSOps, g1.toFSOps)))
  }

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
    assert(Some(true) == z3p.isEquiv(Block(u1.toFSOps, u2.toFSOps), Block(u2.toFSOps, u1.toFSOps)))
  }

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
