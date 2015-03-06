package pipeline.stats

import puppet.syntax._
import puppet.graph._
import pipeline.Facter

object CollectData {

  val env = Facter.run() getOrElse
            (throw new Exception("Facter environment required"))

  val benchmarkroot = "../stats_benchmarks"

  val benchmarks = 
    Map("puppet-bind" -> ("src/tests/server.pp", Some("src/modules")),
        "puppet-git" -> ("src/tests/init.pp", Some("src/modules")),
        "puppet-mosh" -> ("src/tests/init.pp", Some("src/modules")),
        "vagrant-cakephp" -> ("src/manifests/site.pp", Some("src/modules")),
        "vagrantpress" -> ("src/manifests/site.pp", Some("src/modules")),
        "puppet-rbenv" -> ("src/tests/init.pp", Some("src/modules")),
        "devbox" -> ("src/manifests/site.pp", Some("src/modules")),
        // "puppet-nrpe" -> ("src/tests/init.pp", Some("src/manifests"))
        "puppet-monit" -> ("src/tests/init.pp", Some("src/manifests")),
        "puppet-sudo" -> ("src/tests/init.pp", Some("src/manifests"))
        // "yoxos" -> ("src/manifests/standalone.pp", Some("src/modules"))
        // "puppet-activemq" -> ("src/manifests/site.pp", Some("src/modules"))
        // "aventurella" -> ("puppet-vagrant/src/manifests/site.pp", Some("puppet-vagrant/src/modules"))
       )

  def run() {

    for((name, b) <- benchmarks) {

      val mainFilePath = s"${benchmarkroot}/${name}/${b._1}"
      val modulePath = b._2.map((p) => s"${benchmarkroot}/${name}/${p}")

      stats(name, mainFilePath, modulePath, env)
    }
  }

  def stats(name: String,
            mainFile:String, modulePath: Option[String],
            env: Map[String, String]): Int = {
    stats(name, load(mainFile, modulePath), env)
  }

  def stats(name: String,
            program: String,
            env: Map[String, String]): Int = {
    val graph = parse(program).desugar().toGraph(env)
    // printDOTGraph(graph)
    val nresources = graph.nodes.size
    val antichainlength = AntiChainLength(graph)
    println(s"$name $nresources $antichainlength")
    // println()
    // println()
    antichainlength
  }
}
