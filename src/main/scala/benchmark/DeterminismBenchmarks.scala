package rehearsal

object DeterminismBenchmarks {

  import SymbolicEvaluator._

  import PuppetSyntax.{FileScriptGraph}

  def bench(label: String, path: String, check: FileScriptGraph => Boolean, onlySliced: Boolean = false, os: String = "ubuntu-trusty"): Unit = {
    val g = PuppetParser.parseFile(path).eval.resourceGraph.fsGraph(os)

    if (!onlySliced) {
      val (r, t) = time(check(g))
      assert(r == true, s"unexpected result from $label without pruning")
      val size = g.size
      println(s"$label,no-pruning,$size,$t")
    }

    val gPruned = g.pruneWrites()
    val (r, t) = time(check(gPruned))
    assert(r == true, s"unexpected result from $label with pruning")
    val size = gPruned.size
    println(s"$label,pruning,$size,$t")
  }


  val trials = 1
  val root = "parser-tests/good"

  def single(label: String, filename: String, os: String, prune: Boolean): Unit = {
   val g = {
     val g_ = PuppetParser.parseFile(filename).eval.resourceGraph.fsGraph(os)
     if (prune) g_.pruneWrites else g_
   }
   val size = g.size
   val p = if (prune) "pruning" else "no-pruning"
   val (_, t) = time(SymbolicEvaluator.isDeterministic(g))
   println(s"$label, $p, $size, $t")
  }

  def run(): Unit = {
    println("Name,Pruning,Size,Time")
    for (i <- 0.until(trials)) {
      bench("monit", s"$root/dhoppe-monit.pp", g => isDeterministic(g) == true)
      bench("bind", s"$root/thias-bind.pp", g => isDeterministic(g) == true)
      bench("hosting", s"$root/puppet-hosting-fixed.pp", g => isDeterministic(g) == true)
      bench("dns", s"$root/antonlindstrom-powerdns.pp", g => isDeterministic(g) == false)
      // bench("irc", s"$root/spiky-reduced.pp", g => isDeterministic(g) == false, onlySliced = true, os = "centos-6")
      bench("xinetd", s"$root/ghoneycutt-xinetd.pp", g => isDeterministic(g) == false)
      bench("jpa", s"$root/pdurbin-java-jpa-tutorial.pp", g => isDeterministic(g) == true, os = "centos-6")
      bench("ntp", s"$root/thias-ntp.pp", g => isDeterministic(g) == false)
      bench("rsyslog", s"$root/xdrum-rsyslog.pp", g => isDeterministic(g) == false)
      bench("nginx", s"$root/BenoitCattie-puppet-nginx.pp", g => isDeterministic(g) == true)
      bench("amavis", s"$root/mjhas-amavis.pp", g => isDeterministic(g) == true)
      bench("clamav", s"$root/mjhas-clamav.pp", g => isDeterministic(g) == true)
      bench("logstash", s"$root/Nelmo-logstash.pp", g => isDeterministic(g) == false)
    }
  }

}
