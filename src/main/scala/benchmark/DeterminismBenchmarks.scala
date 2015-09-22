package rehearsal

object DeterminismBenchmarks {

  import SymbolicEvaluator._

  def bench(label: String, path: String, check: FileScriptGraph => Boolean, onlySliced: Boolean = false): Unit = {
    val rg = Catalog.parseFile(path)
    val g = toFileScriptGraph(rg)

    if (!onlySliced) {
      val (r, t) = time(check(g))
      assert(r == true, s"unexpected result from $label without slicing")
      val size = fileScriptGraphSize(g)
      println(s"$label,no-slicing,$size,$t")
    }

    val gSliced = Slicing.sliceGraph(g)
    val (r, t) = time(check(gSliced))
    assert(r == true, s"unexpected result from $label with slicing")
    val size = fileScriptGraphSize(gSliced)
    println(s"$label,slicing,$size,$t")
  }


  val root = "rehearsal/src/test/catalogs"

  def run(): Unit = {
    println("Name,Slicing,Size,Time")
    for (i <- 0.until(10)) {
      bench("monit", s"$root/puppet-monit.json", g => isDeterministicError(g) == true)
      bench("bind", s"$root/puppet-bind.json", g => isDeterministic(g) == false)
      bench("hosting", s"$root/puppet-hosting.json", g => isDeterministic(g) == false)
      bench("dns", s"$root/puppet-powerdns.json", g => isDeterministic(g) == false)
      bench("irc", s"$root/SpikyIRC.json", g => isDeterministic(g) == false, onlySliced = true)
      bench("xinetd", s"$root/ghoneycutt-xinetd.json", g => isDeterministic(g) == false)
      bench("ntp", s"$root/thias-ntp.json", g => isDeterministic(g) == false)
      bench("rsyslog", s"$root/xdrum-rsyslog.json", g => isDeterministic(g) == false)
    }
  }

}