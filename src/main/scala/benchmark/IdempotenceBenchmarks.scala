package rehearsal

object IdempotenceBenchmarks {

  import SymbolicEvaluator._

  import PuppetSyntax.{FileScriptGraph}
  import FSSyntax.{Expr}

  def bench(label: String, path: String, check: Expr => Boolean, os: String = "ubuntu-trusty"): Unit = {
    val g = PuppetParser.parseFile(path).eval.resourceGraph.fsGraph(os)

    val gPruned = g.expr().pruneIdem()
    val (r, t) = time(check(gPruned))
    assert(r == true, s"unexpected result from $label with pruning")
    val size = gPruned.size
    println(s"$label,pruning,$size,$t")
  }


  val trials = 1
  val root = "parser-tests/good"

  def run(): Unit = {
    println("Name,Pruning,Size,Time")
    for (i <- 0.until(trials)) {
      bench("monit", s"$root/dhoppe-monit.pp", g => g.isIdempotent == true)
      bench("bind", s"$root/thias-bind.pp", g => g.isIdempotent == true)
      bench("hosting", s"$root/puppet-hosting_deter.pp", g => g.isIdempotent == true)
      bench("dns", s"$root/antonlindstrom-powerdns_deter.pp", g => g.isIdempotent == true)
      bench("irc", s"$root/spiky-reduced-deterministic.pp", g => g.isIdempotent == true, os = "centos-6")
      bench("xinetd", s"$root/ghoneycutt-xinetd_deter.pp", g => g.isIdempotent == true)
      bench("jpa", s"$root/pdurbin-java-jpa-tutorial.pp", g => g.isIdempotent == true, os = "centos-6")
      bench("ntp", s"$root/thias-ntp_deter.pp", g => g.isIdempotent == true)
      bench("rsyslog", s"$root/xdrum-rsyslog_deter.pp", g => g.isIdempotent == true)
      bench("nginx", s"$root/BenoitCattie-puppet-nginx.pp", g => g.isIdempotent == true)
      bench("amavis", s"$root/mjhas-amavis.pp", g => g.isIdempotent == true)
      bench("clamav", s"$root/mjhas-clamav.pp", g => g.isIdempotent == true)
      bench("logstash", s"$root/Nelmo-logstash_deter.pp", g => g.isIdempotent == true)
    }
  }

}
