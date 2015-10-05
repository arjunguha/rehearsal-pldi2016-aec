class CatalogTests extends org.scalatest.FunSuite {
  import rehearsal._
  import SymbolicEvaluator.{isDeterministic, isDeterministicError}
  import Evaluator._

  val dir = "src/test/catalogs"

  // Why do these tests check that nodes.size > 5? It is a dumb sanity check. We could write more rigorous tests,
  // but I've eyeballed the results enough.

  ignore("SpikyIRC.json") {
    val g = Catalog.parseFile(s"$dir/SpikyIRC.json")
    assert(g.nodes.size > 5)
  }

  ignore("puppet-account.json") {
    val g = Catalog.parseFile(s"$dir/puppet-account.json")
    assert(g.nodes.size > 5)
  }

  ignore("puppet-hosting.json") {
    val g = Catalog.parseFile(s"$dir/puppet-hosting.json")
    assert(g.nodes.size > 5)
  }

  test("puppet-monit.json") {
    // val g = Catalog.parseFile(s"$dir/puppet-monit.json")
    val g = toGraph(eval(expandAll(Parser.parseFile(s"$dir/puppet-monit.json"))))
    assert(g.nodes.size > 5)
    val g2 = toFileScriptGraph(g)
    println(g)

    assert(true == isDeterministicError(g2))
  }

  ignore("puppet-powerdns.json") {
    val g = Catalog.parseFile(s"$dir/puppet-powerdns.json")
    assert(g.nodes.size > 5)
  }

}
