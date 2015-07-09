package rehearsal

object DeterminismSizeTables {

  import SymbolicEvaluator._

  def bench(label: String, path: String): Unit = {
    val rg = Catalog.parseFile(path)
    val g = toFileScriptGraph(rg)
    val rSize = rg.nodes.size
    val fSize =  fileScriptGraphSize(g)
    println(s"$label & $rSize & $fSize \\\\")
  }


  val root = "rehearsal/src/test/catalogs"

  def run(): Unit = {
    println("Name & Resources & \\corelang expression size")
    bench("monit", s"$root/puppet-monit.json")
    bench("bind", s"$root/puppet-bind.json")
    bench("hosting", s"$root/puppet-hosting.json")
    bench("dns", s"$root/puppet-powerdns.json")
    bench("irc", s"$root/SpikyIRC.json")
    bench("xinetd", s"$root/ghoneycutt-xinetd.json")
    bench("ntp", s"$root/thias-ntp.json")
    bench("rsyslog", s"$root/xdrum-rsyslog.json")
  }

}