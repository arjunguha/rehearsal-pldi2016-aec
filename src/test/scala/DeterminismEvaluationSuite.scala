class DeterminismEvaluationSuite extends org.scalatest.FunSuite {

  import rehearsal._
  import PuppetParser2.parseFile

  val root = "parser-tests/good"

  test("dhoppe-monit.pp") {
    val g = parseFile(s"$root/dhoppe-monit.pp").eval.resourceGraph.fsGraph
    assert(SymbolicEvaluator.isDeterministicError(g) == true)
  }

  test("thias-bind.pp") {
    val g = parseFile(s"$root/thias-bind.pp").eval.resourceGraph.fsGraph
    assert(SymbolicEvaluator.isDeterministic(g) == false)
  }

  //not in parser-tests yet
  test("puppet-hosting.pp") {
    val g = parseFile(s"$root/puppet-hosting.pp").eval.resourceGraph.fsGraph
    assert(SymbolicEvaluator.isDeterministic(g) == false)
  }

  test("antonlingstrom-powerdns.pp") {
    val g = parseFile(s"$root/antonlingstrom-powerdns.pp").eval.resourceGraph.fsGraph
    assert(SymbolicEvaluator.isDeterministic(g) == false)
  }

  ignore("nfisher-SpikyIRC.pp") {
    val g = parseFile(s"$root/nfisher-SpikyIRC.pp").eval.resourceGraph.fsGraph
    assert(SymbolicEvaluator.isDeterministic(Slicing.sliceGraph(g)) == false)
  }

  test("ghoneycutt-xinetd.pp") {
    val g = parseFile(s"$root/ghoneycutt-xinetd.pp").eval.resourceGraph.fsGraph
    assert(SymbolicEvaluator.isDeterministic(g) == false)
  }

  //not in parser-tests yet
  ignore("thias-ntp.pp") {
    val g = parseFile(s"$root/thias-ntp.pp").eval.resourceGraph.fsGraph
    assert(SymbolicEvaluator.isDeterministic(g) == false)
  }

  //not in parser-tests yet
  test("xdrum-rsyslog.pp") {
    val g = parseFile(s"$root/xdrum-rsyslog.pp").eval.resourceGraph.fsGraph
    assert(SymbolicEvaluator.isDeterministic(g) == false)
  }
}