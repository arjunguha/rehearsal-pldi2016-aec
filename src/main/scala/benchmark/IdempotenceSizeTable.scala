package rehearsal

object IdempotenceSizeTables {

  import SymbolicEvaluator._

  def bench(label: String, path: String, os: String = "ubuntu-trusty"): Unit = {
    val rg = PuppetParser.parseFile(path).eval().resourceGraph()
    val g = rg.fsGraph(os)
    val rSize = rg.deps.nodes.size
    val fSize =  g.size
    println(s"$label & $rSize & $fSize \\\\")
  }


  val root = "parser-tests/good"

  def run(): Unit = {
    bench("monit", s"$root/dhoppe-monit.pp")
    bench("bind", s"$root/thias-bind.pp")
    bench("hosting", s"$root/puppet-hosting_deter.pp")
    bench("dns", s"$root/antonlindstrom-powerdns_deter.pp")
    bench("irc", s"$root/spiky-reduced-deterministic.pp", os = "centos-6")
    bench("xinetd", s"$root/ghoneycutt-xinetd_deter.pp")
    bench("jpa", s"$root/pdurbin-java-jpa-tutorial.pp", os = "centos-6")
    bench("ntp", s"$root/thias-ntp_deter.pp")
    bench("rsyslog", s"$root/xdrum-rsyslog_deter.pp")
    bench("nginx", s"$root/BenoitCattie-puppet-nginx.pp")
    bench("amavis", s"$root/mjhas-amavis.pp")
    bench("clamav", s"$root/mjhas-clamav.pp")
    bench("logstash", s"$root/Nelmo-logstash_deter.pp")
  }

}