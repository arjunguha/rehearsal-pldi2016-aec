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
    val g = parseFile(s"$root/dhoppe-monit.pp").eval.resourceGraph.fsGraph("ubuntu-trusty")
    assert(SymbolicEvaluator.isDeterministic(g) == true)
  }

  test("dhoppe-monit_BUG.pp") {
    val g = parseFile(s"$root/dhoppe-monit_BUG.pp").eval.resourceGraph.fsGraph("ubuntu-trusty")
    assert(SymbolicEvaluator.isDeterministicError(g) == true)
  }

  test("thias-bind.pp") {
    val g = parseFile(s"$root/thias-bind.pp").eval.resourceGraph.fsGraph("ubuntu-trusty")
    assert(SymbolicEvaluator.isDeterministic(Slicing.sliceGraph(g)) == true)
  }

  test("thias-bind-buggy.pp") {
    val g = parseFile(s"$root/thias-bind-buggy.pp").eval.resourceGraph.fsGraph("centos-6")
    assert(SymbolicEvaluator.isDeterministicError(Slicing.sliceGraph(g)) == false)
    assert(SymbolicEvaluator.isDeterministic(Slicing.sliceGraph(g)) == false)
  }

  test("puppet-hosting.pp") {
    intercept[PackageNotFound] {
      val g = parseFile(s"$root/puppet-hosting.pp").eval.resourceGraph.fsGraph("ubuntu-trusty")
      // TODO(arjun): This line shouldn't be necessary, but .fsGraph produces a lazy data structure!s
      assert(SymbolicEvaluator.isDeterministic(g) == false)
    }
  }

  test("antonlindstrom-powerdns.pp") {
    val g = parseFile(s"$root/antonlindstrom-powerdns.pp").eval.resourceGraph.fsGraph("ubuntu-trusty")
    assert(SymbolicEvaluator.isDeterministic(g) == false)
  }

  ignore("nfisher-SpikyIRC.pp") {
    val g = parseFile(s"$root/nfisher-SpikyIRC.pp").eval.resourceGraph.fsGraph("centos-6")
    assert(SymbolicEvaluator.isDeterministic(Slicing.sliceGraph(g)) == false)
  }

  val spikyGraph = FSGraph(Map(
      Node("package","rrdtool") -> If(TestFileState("/x", IsDir), Skip, Mkdir("/x")),
      Node("file","swap") ->
        Seq(If(TestFileState("/x/swap.conf", IsFile), Rm("/x/swap.conf"), Skip),
            CreateFile("/x/swap.conf", "")
        )
    ), Graph(Node("package","rrdtool"), Node("file","swap")))

  test("spiky-reduced.pp Pruned") {
    val sliced = Slicing.sliceGraph(spikyGraph)
    assert(SymbolicEvaluator.isDeterministic(sliced) == false)
  }

  test("spiky-reduced.pp Not pruned") {
    assert(SymbolicEvaluator.isDeterministic(spikyGraph) == false)
  }

  test("ghoneycutt-xinetd.pp") {
    val g = parseFile(s"$root/ghoneycutt-xinetd.pp").eval.resourceGraph.fsGraph("ubuntu-trusty")
    assert(SymbolicEvaluator.isDeterministic(g) == false)
  }

  test("mjhas-amavis.pp") {
    val g = parseFile(s"$root/mjhas-amavis.pp").eval.resourceGraph.fsGraph("ubuntu-trusty")
    assert(SymbolicEvaluator.isDeterministic(g))
  }

  test("mjhas-clamav.pp") {
    val g = parseFile(s"$root/mjhas-clamav.pp").eval.resourceGraph.fsGraph("ubuntu-trusty")
    assert(SymbolicEvaluator.isDeterministic(g))
  }

  test("pdurbin-java-jpa-tutorial.pp") {
    val g = parseFile(s"$root/pdurbin-java-jpa-tutorial.pp").eval.resourceGraph.fsGraph("centos-6")
    assert(SymbolicEvaluator.isDeterministic(Slicing.sliceGraph(g)) == true)
  }

  test("thias-ntp.pp") {
    val g = parseFile(s"$root/thias-ntp.pp").eval.resourceGraph.fsGraph("ubuntu-trusty")
    assert(SymbolicEvaluator.isDeterministic(g) == false)
  }

  test("xdrum-rsyslog.pp") {
    val g = parseFile(s"$root/xdrum-rsyslog.pp").eval.resourceGraph.fsGraph("ubuntu-trusty")
    assert(SymbolicEvaluator.isDeterministic(g) == false)
  }

  test("BenoitCattie-puppet-nginx.pp") {
    val g = parseFile(s"$root/BenoitCattie-puppet-nginx.pp").eval.resourceGraph.fsGraph("ubuntu-trusty")
    assert(SymbolicEvaluator.isDeterministic(g))
  }

}
