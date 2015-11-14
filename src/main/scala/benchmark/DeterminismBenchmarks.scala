package rehearsal

object DeterminismBenchmarks {

  import SymbolicEvaluator._

  import PuppetSyntax.{FileScriptGraph}

  def bench(label: String, path: String, check: FileScriptGraph => Option[Boolean], expected: Boolean, onlySliced: Boolean = false, os: String = "ubuntu-trusty"): Unit = {
    val g = PuppetParser.parseFile(path).eval.resourceGraph.fsGraph(os)

    def checkAndOutput(res: (Option[Boolean], Long), pruning: String, size: Int) = res match {
      case (Some(out), t) => {
        assert(out == expected, s"unexpected result from $label with $pruning")
        println(s"$label,no-pruning,$size,$t")
      }
      case (None, _) => println(s"$label,$pruning,$size,timedout")
    }

    if (!onlySliced) {
      checkAndOutput(time(check(g)), "no-pruning", g.size)
    }

    val gPruned = g.pruneWrites()
    checkAndOutput(time(check(gPruned)), "pruning", gPruned.size)
  }


  val trials = 1
  val root = "parser-tests/good"

  def checkWithTimeout(g: FileScriptGraph) = isDeterministicWithTimeout(g, 15 * 60)

  def run(): Unit = {
    println("Name,Pruning,Size,Time")
    for (i <- 0.until(trials)) {
      bench("monit", s"$root/dhoppe-monit.pp", checkWithTimeout, true)
      bench("bind", s"$root/thias-bind.pp", checkWithTimeout, true)
      bench("hosting", s"$root/puppet-hosting-fixed.pp", checkWithTimeout, true)
      bench("dns", s"$root/antonlindstrom-powerdns.pp", checkWithTimeout, false)
      bench("irc", s"$root/spiky-reduced.pp", checkWithTimeout, false, onlySliced = true, os = "centos-6")
      bench("xinetd", s"$root/ghoneycutt-xinetd.pp", checkWithTimeout, false)
      bench("jpa", s"$root/pdurbin-java-jpa-tutorial.pp", checkWithTimeout, true, os = "centos-6")
      bench("ntp", s"$root/thias-ntp.pp", checkWithTimeout, false)
      bench("rsyslog", s"$root/xdrum-rsyslog.pp", checkWithTimeout, false)
      bench("nginx", s"$root/BenoitCattie-puppet-nginx.pp", checkWithTimeout, true)
      bench("amavis", s"$root/mjhas-amavis.pp", checkWithTimeout, true)
      bench("clamav", s"$root/mjhas-clamav.pp", checkWithTimeout, true)
      bench("logstash", s"$root/Nelmo-logstash.pp", checkWithTimeout, false)
    }
  }

}
