package rehearsal

object IdempotenceBenchmarks {

  import SymbolicEvaluator._

  import PuppetSyntax.{FileScriptGraph}
  import FSSyntax.{Expr}

  def bench(label: String, path: String, expected: Boolean, os: String = "ubuntu-trusty"): Unit = {
    val g = PuppetParser.parseFile(path).eval.resourceGraph.fsGraph(os)

    def checkAndOutput(res: (Boolean, Long), pruning: String, size: Int) = res match {
      case (out, t) => {
        assert(out == expected, s"unexpected result from $label with $pruning")
        println(s"$label,$pruning,$size,$t")
      }
    }

    checkAndOutput(time(isIdempotent(g)), "no-pruning", g.size)
    val gPruned = g.expr().pruneIdem()
    checkAndOutput(time(gPruned.isIdempotent), "pruning", gPruned.size)
  }


  val trials = 1
  val root = "parser-tests/good"

  def run(): Unit = {
    println("IName,IdemPruning,ISize,ITime")
    for (i <- 0.until(trials)) {
      bench("monit", s"$root/dhoppe-monit.pp", true)
      bench("bind", s"$root/thias-bind.pp", true)
      bench("hosting", s"$root/puppet-hosting_deter.pp", true)
      bench("dns", s"$root/antonlindstrom-powerdns_deter.pp", true)
      bench("irc", s"$root/spiky-reduced-deterministic.pp", true, os = "centos-6")
      bench("xinetd", s"$root/ghoneycutt-xinetd_deter.pp", true)
      bench("jpa", s"$root/pdurbin-java-jpa-tutorial.pp", true, os = "centos-6")
      bench("ntp", s"$root/thias-ntp_deter.pp", true)
      bench("rsyslog", s"$root/xdrum-rsyslog_deter.pp", true)
      bench("nginx", s"$root/BenoitCattie-puppet-nginx.pp", true)
      bench("amavis", s"$root/mjhas-amavis.pp", true)
      bench("clamav", s"$root/mjhas-clamav.pp", true)
      bench("logstash", s"$root/Nelmo-logstash_deter.pp", true)
    }
  }

}
