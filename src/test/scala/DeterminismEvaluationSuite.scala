class DeterminismEvaluationSuite extends FunSuitePlus
  with org.scalatest.BeforeAndAfterEach {

  import rehearsal._
  import PuppetParser.parseFile
  import rehearsal.Implicits._
  import SymbolicEvaluator.{predEquals, exprEquals, isDeterministic, isDeterministicError}
  import PuppetSyntax._

  val root = "parser-tests/good"

  override def beforeEach() = {
    FSSyntax.clearCache()
  }

  def mytest(filename: String,
             isDeterministic: Boolean,
             os: String = "ubuntu-trusty",
             onlyPrune: Boolean = true): Unit = {
    test(filename) {
      val g = parseFile(s"$root/$filename").eval.resourceGraph.fsGraph(os)

      if (onlyPrune == false) {
        val (r, t) = time(g.toExecTree.isDeterministic)
        info(s"Took ${t}ms without pruning")
        assert(r == isDeterministic,
          s"without pruning, expected $filename to be " +
            (if (isDeterministic) "deterministic" else "non-deterministic"))

      }

      val (r, t) = time(g.pruneWrites.toExecTree.isDeterministic)
      info(s"Took ${t}ms with pruning")
      assert(r ==
        isDeterministic,
        s"with pruning, expected $filename to be " +
          (if (isDeterministic) "deterministic" else "non-deterministic"))
    }
  }

  mytest("dhoppe-monit.pp", true)
  mytest("thias-bind.pp", true, os = "centos-6")

  test("dhoppe-monit_BUG.pp") {
    val g = parseFile(s"$root/dhoppe-monit_BUG.pp").eval.resourceGraph.fsGraph("ubuntu-trusty")
    assert(SymbolicEvaluator.isDeterministicError(g) == true)
  }



  mytest("thias-bind-buggy.pp", false, os = "centos-6")

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

  mytest("antonlindstrom-powerdns.pp", false)
  mytest("antonlindstrom-powerdns_deter.pp", true)
  mytest("nfisher-SpikyIRC.pp", false, os = "centos-6", onlyPrune = false)
  mytest("spiky-reduced.pp", false, os = "centos-6")
  mytest("spiky-reduced-deterministic.pp", true, os = "centos-6")
  mytest("ghoneycutt-xinetd.pp", false)
  mytest("ghoneycutt-xinetd_deter.pp", true)
  mytest("mjhas-amavis.pp", true)
  mytest("mjhas-clamav.pp", true)
  mytest("clamav-reduced.pp", true)
  mytest("Nelmo-logstash.pp", false)
  mytest("Nelmo-logstash_deter.pp", true)
  mytest("pdurbin-java-jpa-tutorial.pp", true, os = "centos-6")
  mytest("thias-ntp.pp", false)
  mytest("thias-ntp_deter.pp", true)
  mytest("xdrum-rsyslog.pp", false)
  mytest("xdrum-rsyslog_deter.pp", true)
  mytest("BenoitCattie-puppet-nginx.pp", true)

}
