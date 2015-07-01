class CatalogTests extends org.scalatest.FunSuite {
  import rehearsal._

  val dir = "rehearsal/src/test/catalogs"

  // Why do these tests check that nodes.size > 5? It is a dumb sanity check. We could write more rigorous tests,
  // but I've eyeballed the results enough.

  test("SpikyIRC.json") {
    val g = Catalog.parseFile(s"$dir/SpikyIRC.json")
    assert(g.nodes.size > 5)
  }

  test("puppet-account.json") {
    val g = Catalog.parseFile(s"$dir/puppet-account.json")
    assert(g.nodes.size > 5)
  }

  test("puppet-hosting.json") {
    val g = Catalog.parseFile(s"$dir/puppet-hosting.json")
    assert(g.nodes.size > 5)
  }

  test("puppet-monit.json") {
    val g = Catalog.parseFile(s"$dir/puppet-monit.json")
    assert(g.nodes.size > 5)
  }

  test("puppet-powerdns.json") {
    val g = Catalog.parseFile(s"$dir/puppet-powerdns.json")
    assert(g.nodes.size > 5)
  }

}
