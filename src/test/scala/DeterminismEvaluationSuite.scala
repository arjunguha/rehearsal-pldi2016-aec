class DeterminismEvaluationSuite extends org.scalatest.FunSuite {

  import rehearsal._
  import java.nio.file._
  import Evaluator._

  val root = "parser-tests/good"

  test("dhoppe-monit.pp") {
    val rg = toGraph(eval(expandAll(Parser.parseFile(s"$root/dhoppe-monit.pp"))))
    val g = toFileScriptGraph(rg)
    assert(SymbolicEvaluator.isDeterministicError(g) == true)
  }

  test("thias-bind.pp") {
    val rg = toGraph(eval(expandAll(Parser.parseFile(s"$root/thias-bind.pp"))))
    val g = toFileScriptGraph(rg)
    assert(SymbolicEvaluator.isDeterministic(g) == false)
  }

  //not in parser-tests yet
  ignore("puppet-hosting.pp") {
    val rg = toGraph(eval(expandAll(Parser.parseFile(s"$root/puppet-hosting.pp"))))
    val g = toFileScriptGraph(rg)
    assert(SymbolicEvaluator.isDeterministic(g) == false)
  }

  test("antonlingstrom-powerdns.pp") {
    val rg = toGraph(eval(expandAll(Parser.parseFile(s"$root/antonlingstrom-powerdns.pp"))))
    val g = toFileScriptGraph(rg)
    assert(SymbolicEvaluator.isDeterministic(g) == false)
  }

  test("nfisher-SpikyIRC.pp") {
    val rg = toGraph(eval(expandAll(Parser.parseFile(s"$root/nfisher-SpikyIRC.pp"))))
    val g = toFileScriptGraph(rg)
    assert(SymbolicEvaluator.isDeterministic(Slicing.sliceGraph(g)) == false)
  }

  //not in parser-tests yet
  ignore("ghoneycutt-xinetd.pp") {
    val rg = toGraph(eval(expandAll(Parser.parseFile(s"$root/ghoneycutt-xinetd.pp"))))
    val g = toFileScriptGraph(rg)
    assert(SymbolicEvaluator.isDeterministic(g) == false)
  }

  //not in parser-tests yet
  ignore("thias-ntp.pp") {
    val rg = toGraph(eval(expandAll(Parser.parseFile(s"$root/thias-ntp.pp"))))
    val g = toFileScriptGraph(rg)
    assert(SymbolicEvaluator.isDeterministic(g) == false)
  }

  //not in parser-tests yet
  ignore("xdrum-rsyslog.pp") {
    val rg = toGraph(eval(expandAll(Parser.parseFile(s"$root/xdrum-rsyslog.pp"))))
    val g = toFileScriptGraph(rg)
    assert(SymbolicEvaluator.isDeterministic(g) == false)
  }
}