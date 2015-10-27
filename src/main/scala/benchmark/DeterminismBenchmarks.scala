package rehearsal

object DeterminismBenchmarks {

  import SymbolicEvaluator._

  import PuppetSyntax.{FileScriptGraph}

  def bench(label: String, path: String, check: FileScriptGraph => Boolean, onlySliced: Boolean = false): Unit = {
    val g = PuppetParser.parseFile(path).eval.resourceGraph.fsGraph("ubuntu-trusty")

    if (!onlySliced) {
      val (r, t) = time(check(g))
      assert(r == true, s"unexpected result from $label without slicing")
      val size = g.size
      println(s"$label,no-slicing,$size,$t")
    }

    val gSliced = Slicing.sliceGraph(g)
    val (r, t) = time(check(gSliced))
    assert(r == true, s"unexpected result from $label with slicing")
    val size = gSliced.size
    println(s"$label,slicing,$size,$t")
  }


  val root = "rehearsal/parser-tests/good"

  def run(): Unit = {
    println("Name,Slicing,Size,Time")
    for (i <- 0.until(10)) {
      bench("monit", s"$root/dhoppe-monit.pp", g => isDeterministic(g) == true)
      bench("bind", s"$root/thias-bind.pp", g => isDeterministic(g) == true)
      bench("hosting", s"$root/puppet-hosting.pp", g => isDeterministic(g) == false)
      bench("dns", s"$root/antonlingstrom-powerdns.pp", g => isDeterministic(g) == false)
      bench("irc", s"$root/nfisher-SpikyIRC.pp", g => isDeterministic(g) == false, onlySliced = true)
      bench("xinetd", s"$root/ghoneycutt-xinetd.pp", g => isDeterministic(g) == false)
      bench("apache", s"$root/gazinzhou-apache.pp", g => isDeterministic(g) == true)
      bench("jpa", s"$root/pdurbin-java-jpa-tutorial.pp", g => isDeterministic(g) == true)
      bench("ntp", s"$root/thias-ntp.pp", g => isDeterministic(g) == false)
      bench("rsyslog", s"$root/xdrum-rsyslog.pp", g => isDeterministic(g) == false)
      bench("nginx", s"$root/BenoitCattie-puppet-nginx.pp", g => isDeterministic(g) == true)
    }
  }

}