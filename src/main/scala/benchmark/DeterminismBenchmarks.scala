package rehearsal

object DeterminismBenchmarks {

  import SymbolicEvaluator._

  import PuppetSyntax.{FileScriptGraph}

  def check(args: Seq[String]): Boolean = {
    import scala.concurrent._
    import ExecutionContext.Implicits.global
    import scala.sys.process._

    val p = args.run()
    val f = Future(blocking(p.exitValue())) // wrap in Future
    try {
        Await.result(f, duration.Duration(600, "sec"))
        true
      } catch {
        case _: TimeoutException =>
          p.destroy()
          false
      }
  }

  def bench(label: String, path: String, onlySliced: Boolean = false, os: String = "ubuntu-trusty"): Unit = {
    val g = PuppetParser.parseFile(path).eval.resourceGraph.fsGraph(os)
    import scala.sys.process._

    if (check(Seq("./run.sh", "deterbench", label, path, os, "prune")) == false) {
      println(s"$label, pruning, 0, 0")
    }
    if (onlySliced != true) {
      if (check(Seq("./run.sh", "deterbench", label, path, os, "noprune")) == false) {
        println(s"$label, no-pruning, 0, 0")
      }
    }
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
      bench("monit", s"$root/dhoppe-monit.pp")
      bench("bind", s"$root/thias-bind.pp")
      bench("hosting", s"$root/puppet-hosting_fixed.pp")
      bench("dns", s"$root/antonlindstrom-powerdns.pp")
      bench("irc", s"$root/spiky-reduced.pp",  os = "centos-6")
      bench("xinetd", s"$root/ghoneycutt-xinetd.pp")
      bench("jpa", s"$root/pdurbin-java-jpa-tutorial.pp", os = "centos-6")
      bench("ntp", s"$root/thias-ntp.pp")
      bench("rsyslog", s"$root/xdrum-rsyslog.pp")
      bench("nginx", s"$root/BenoitCattie-puppet-nginx.pp")
      bench("amavis", s"$root/mjhas-amavis.pp")
      bench("clamav", s"$root/mjhas-clamav.pp")
      bench("logstash", s"$root/Nelmo-logstash.pp")
    }
  }

}
