class DeterminismEvaluationSuite extends org.scalatest.FunSuite {

  import rehearsal._
  import java.nio.file._

  val root = "rehearsal/src/test/catalogs"

  test("puppet-account.json") {
    val rg = Catalog.parseFile(s"$root/puppet-account.json")
    val g = toFileScriptGraph(rg)
    assert(SymbolicEvaluator.isDeterministic(g) == false)
  }

  test("puppet-monit.json") {
    val rg = Catalog.parseFile(s"$root/puppet-monit.json")
    val g = toFileScriptGraph(rg)
    assert(SymbolicEvaluator.isDeterministic(g) == false)
  }

  test("puppet-bind.json") {
    val rg = Catalog.parseFile(s"$root/puppet-bind.json")
    val g = toFileScriptGraph(rg)
    assert(SymbolicEvaluator.isDeterministic(g) == false)
  }

  test("puppet-hosting.json") {
    val rg = Catalog.parseFile(s"$root/puppet-hosting.json")
    val g = toFileScriptGraph(rg)
    assert(SymbolicEvaluator.isDeterministic(g) == false)
  }

  test("puppet-powerdns.json") {
    val rg = Catalog.parseFile(s"$root/puppet-powerdns.json")
    val g = toFileScriptGraph(rg)
    assert(SymbolicEvaluator.isDeterministic(g) == false)
  }

  test("SpikyIRC.json") {
    val rg = Catalog.parseFile(s"$root/SpikyIRC.json")
    val g = toFileScriptGraph(rg)
    assert(SymbolicEvaluator.isDeterministic(Slicing.sliceGraph(g)) == false)
  }

  test("ghoneycutt-xinetd.json") {
    val rg = Catalog.parseFile(s"$root/ghoneycutt-xinetd.json")
    val g = toFileScriptGraph(rg)
    assert(SymbolicEvaluator.isDeterministic(g) == false)
  }

  test("thias-ntp.json") {
    val rg = Catalog.parseFile(s"$root/thias-ntp.json")
    val g = toFileScriptGraph(rg)
    assert(SymbolicEvaluator.isDeterministic(g) == false)
  }

  test("xdrum-rsyslog.json") {
    val rg = Catalog.parseFile(s"$root/xdrum-rsyslog.json")
    val g = toFileScriptGraph(rg)
    assert(SymbolicEvaluator.isDeterministic(g) == false)
  }



}