class DeterminismEvaluationSuite extends FunSuitePlus
  with org.scalatest.BeforeAndAfterEach {

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

  override def beforeEach() = {
    FSSyntax.clearCache()
  }

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
    assert(SymbolicEvaluator.isDeterministic(g.pruneWrites()) == true)
  }

  test("thias-bind-buggy.pp") {
    val g = parseFile(s"$root/thias-bind-buggy.pp").eval.resourceGraph.fsGraph("centos-6")
    assert(SymbolicEvaluator.isDeterministic(g.pruneWrites()) == false)
  }

  test("puppet-hosting.pp") {
    intercept[PackageNotFound] {
      val g = parseFile(s"$root/puppet-hosting.pp").eval.resourceGraph.fsGraph("ubuntu-trusty")
      // TODO(arjun): This line shouldn't be necessary, but .fsGraph produces a lazy data structure!s
      assert(SymbolicEvaluator.isDeterministic(g) == false)
    }
  }

  test("puppet-hosting_deter.pp") {
    val g = parseFile(s"$root/puppet-hosting_deter.pp").eval.resourceGraph.fsGraph("ubuntu-trusty")
    // TODO(arjun): This line shouldn't be necessary, but .fsGraph produces a lazy data structure!s
    assert(SymbolicEvaluator.isDeterministic(g) == true)
  }

  test("antonlindstrom-powerdns.pp") {
    val g = parseFile(s"$root/antonlindstrom-powerdns.pp").eval.resourceGraph.fsGraph("ubuntu-trusty")
    assert(SymbolicEvaluator.isDeterministic(g) == false)
  }

  test("antonlindstrom-powerdns_deter.pp") {
    val g = parseFile(s"$root/antonlindstrom-powerdns_deter.pp").eval.resourceGraph.fsGraph("ubuntu-trusty")
    assert(SymbolicEvaluator.isDeterministic(g) == true)
  }

  test("nfisher-SpikyIRC.pp") {
    val g = parseFile(s"$root/nfisher-SpikyIRC.pp").eval.resourceGraph.fsGraph("centos-6")
    assert(SymbolicEvaluator.isDeterministic(g.pruneWrites()) == false)
  }

  test("spiky-reduced.pp pruned") {
    val g = parseFile(s"$root/spiky-reduced.pp").eval.resourceGraph.fsGraph("centos-6").pruneWrites()
    assert(SymbolicEvaluator.isDeterministic(g) == false)
  }

  test("spiky-reduced-deterministic.pp pruned") {
    val g = parseFile(s"$root/spiky-reduced-deterministic.pp").eval.resourceGraph.fsGraph("centos-6").pruneWrites()
    assert(SymbolicEvaluator.isDeterministic(g) == true)
  }

  test("ghoneycutt-xinetd.pp") {
    val g = parseFile(s"$root/ghoneycutt-xinetd.pp").eval.resourceGraph.fsGraph("ubuntu-trusty")
    assert(SymbolicEvaluator.isDeterministic(g) == false)
  }

  test("ghoneycutt-xinetd_deter.pp") {
    val g = parseFile(s"$root/ghoneycutt-xinetd_deter.pp").eval.resourceGraph.fsGraph("ubuntu-trusty")
    assert(SymbolicEvaluator.isDeterministic(g) == true)
  }

  test("mjhas-amavis.pp") {
    val g = parseFile(s"$root/mjhas-amavis.pp").eval.resourceGraph.fsGraph("ubuntu-trusty")
    assert(SymbolicEvaluator.isDeterministic(g))
  }

  test("mjhas-clamav.pp") {
    val g = parseFile(s"$root/mjhas-clamav.pp").eval.resourceGraph.fsGraph("ubuntu-trusty")
    assert(SymbolicEvaluator.isDeterministic(g))
  }

  test("Nelmo-logstash.pp") {
    val g = parseFile(s"$root/Nelmo-logstash.pp").eval.resourceGraph.fsGraph("ubuntu-trusty")
    assert(SymbolicEvaluator.isDeterministic(g) == false)
  }

 test("Nelmo-logstash_deter.pp") {
    val g = parseFile(s"$root/Nelmo-logstash_deter.pp").eval.resourceGraph.fsGraph("ubuntu-trusty")
    assert(SymbolicEvaluator.isDeterministic(g) == true)
  }

  test("pdurbin-java-jpa-tutorial.pp (with pruning)") {
    val g = parseFile(s"$root/pdurbin-java-jpa-tutorial.pp").eval.resourceGraph.fsGraph("centos-6")
    assert(SymbolicEvaluator.isDeterministic(g.pruneWrites()) == true)
  }

  test("thias-ntp.pp") {
    val g = parseFile(s"$root/thias-ntp.pp").eval.resourceGraph.fsGraph("ubuntu-trusty")
    assert(SymbolicEvaluator.isDeterministic(g) == false)
  }

  test("thias-ntp_deter.pp") {
    val g = parseFile(s"$root/thias-ntp_deter.pp").eval.resourceGraph.fsGraph("ubuntu-trusty")
    assert(SymbolicEvaluator.isDeterministic(g) == true)
  }

  test("xdrum-rsyslog.pp") {
    val g = parseFile(s"$root/xdrum-rsyslog.pp").eval.resourceGraph.fsGraph("ubuntu-trusty")
    assert(SymbolicEvaluator.isDeterministic(g) == false)
  }

  test("xdrum-rsyslog_deter.pp") {
    val g = parseFile(s"$root/xdrum-rsyslog_deter.pp").eval.resourceGraph.fsGraph("ubuntu-trusty")
    assert(SymbolicEvaluator.isDeterministic(g) == true)
  }

  test("BenoitCattie-puppet-nginx.pp") {
    val g = parseFile(s"$root/BenoitCattie-puppet-nginx.pp").eval.resourceGraph.fsGraph("ubuntu-trusty")
    assert(SymbolicEvaluator.isDeterministic(g))
  }

}
