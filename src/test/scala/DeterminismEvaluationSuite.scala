class DeterminismEvaluationSuite extends org.scalatest.FunSuite {

  import rehearsal._
  import PuppetParser.parseFile

  import FSSyntax._
  import scalax.collection.Graph
  import scalax.collection.GraphEdge.DiEdge
  import rehearsal.Implicits._
  import java.nio.file.Paths
  import SymbolicEvaluator.{predEquals, exprEquals, isDeterministic, isDeterministicError}
  import PuppetSyntax._

  val root = "parser-tests/good"

  test("dhoppe-monit.pp") {
    val g = parseFile(s"$root/dhoppe-monit.pp").eval.resourceGraph.fsGraph
    assert(SymbolicEvaluator.isDeterministic(g) == true)
  }

  test("dhoppe-monit_BUG.pp") {
    val g = parseFile(s"$root/dhoppe-monit_BUG.pp").eval.resourceGraph.fsGraph
    assert(SymbolicEvaluator.isDeterministicError(g) == true)
  }

  test("thias-bind.pp") {
    val g = parseFile(s"$root/thias-bind.pp").eval.resourceGraph.fsGraph
    assert(SymbolicEvaluator.isDeterministic(Slicing.sliceGraph(g)) == true)
  }

  test("thias-bind-buggy.pp") {
    val g = parseFile(s"$root/thias-bind-buggy.pp").eval.resourceGraph.fsGraph()
    assert(SymbolicEvaluator.isDeterministicError(Slicing.sliceGraph(g)) == false)
    assert(SymbolicEvaluator.isDeterministic(Slicing.sliceGraph(g)) == false)
  }

  test("puppet-hosting.pp") {
    val g = parseFile(s"$root/puppet-hosting.pp").eval.resourceGraph.fsGraph
    assert(SymbolicEvaluator.isDeterministic(g) == false)
  }

  test("antonlindstrom-powerdns.pp") {
    val g = parseFile(s"$root/antonlindstrom-powerdns.pp").eval.resourceGraph.fsGraph
    assert(SymbolicEvaluator.isDeterministic(g) == false)
  }

  ignore("nfisher-SpikyIRC.pp") {
    val g = parseFile(s"$root/nfisher-SpikyIRC.pp").eval.resourceGraph.fsGraph
    val homeSlice = Slicing.sliceGraph(g)
    println(homeSlice.exprs)
    assert(SymbolicEvaluator.isDeterministic(Slicing.sliceGraph(g)) == false)
  }

  test("ghoneycutt-xinetd.pp") {
    val g = parseFile(s"$root/ghoneycutt-xinetd.pp").eval.resourceGraph.fsGraph
    assert(SymbolicEvaluator.isDeterministic(g) == false)
  }

  test("pdurbin-java-jpa-tutorial.pp") {
    val g = parseFile(s"$root/pdurbin-java-jpa-tutorial.pp").eval.resourceGraph.fsGraph
    assert(SymbolicEvaluator.isDeterministic(Slicing.sliceGraph(g)) == true)
  }

  test("thias-ntp.pp") {
    val g = parseFile(s"$root/thias-ntp.pp").eval.resourceGraph.fsGraph
    assert(SymbolicEvaluator.isDeterministic(g) == false)
  }

  test("xdrum-rsyslog.pp") {
    val g = parseFile(s"$root/xdrum-rsyslog.pp").eval.resourceGraph.fsGraph
    assert(SymbolicEvaluator.isDeterministic(g) == false)
  }

  test("BenoitCattie-puppet-nginx.pp") {
    val g = parseFile(s"$root/BenoitCattie-puppet-nginx.pp").eval.resourceGraph.fsGraph
    assert(SymbolicEvaluator.isDeterministic(g))
  }
}
