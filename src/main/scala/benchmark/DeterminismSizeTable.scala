package rehearsal

object DeterminismSizeTables {

  import SymbolicEvaluator._

  var data: Set[(String, Int, Int, Int)] = Set()

  def bench(label: String, path: String, os: String = "ubuntu-trusty") {
    val rg = PuppetParser.parseFile(path).eval().resourceGraph()
    val g = rg.fsGraph(os)
    val rSize = rg.deps.nodes.size
    val paths = g.expr.fileSets.writes.size
    val postPruningPaths =  g.pruneWrites.expr.fileSets.writes.size
    data = data + ((label, rSize, paths, postPruningPaths))
  }

  def printCSV() {
    for ((label, size, paths, postPruningPaths) <- data) {
      println(s"$label, $size, $paths, $postPruningPaths")
    }
  }

  def printTable() {
    for ((label, size, paths, postPruningPaths) <- data) {
      println(s"$label & $size & $paths & $postPruningPaths \\\\")
    }

  }

  val root = "parser-tests/good"

  def run(): Unit = {
    bench("monit", s"$root/dhoppe-monit.pp")
    bench("bind", s"$root/thias-bind.pp")
    bench("hosting", s"$root/puppet-hosting_deter.pp")
    bench("dns", s"$root/antonlindstrom-powerdns.pp")
    bench("irc", s"$root/spiky-reduced.pp", os = "centos-6")
    bench("xinetd", s"$root/ghoneycutt-xinetd.pp")
    bench("jpa", s"$root/pdurbin-java-jpa-tutorial.pp", os = "centos-6")
    bench("ntp", s"$root/thias-ntp.pp")
    bench("rsyslog", s"$root/xdrum-rsyslog.pp")
    bench("nginx", s"$root/BenoitCattie-puppet-nginx.pp")
    bench("amavis", s"$root/mjhas-amavis.pp")
    bench("clamav", s"$root/mjhas-clamav.pp")
    bench("logstash", s"$root/Nelmo-logstash.pp")
    printTable()
    printCSV()
  }

}
