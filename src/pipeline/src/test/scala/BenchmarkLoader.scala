import pipeline._



object BenchmarkLoader {

  private val facterEnv = Facter.run() getOrElse
                            (throw new Exception("Facter environment required"))

  // TODO(arjun): Should be in scala-puppet
  private def loadBenchmark(bench: (String, Option[String])): puppet.core.BlockStmtC = {
    val (mainFile, modulePath) = bench
    puppet.syntax.parse(puppet.syntax.load(mainFile, modulePath)).desugar()
  }

  private def fixPaths(benchWithName: ((String, (String, Option[String])))) = {
    val (name, (mainFile, modulePath)) = benchWithName
    val mainFileFixed = s"../benchmarks/$name/$mainFile"
    val modulePathFixed = modulePath.map(p => s"../benchmarks/$name/$p")
    name -> (mainFileFixed -> modulePathFixed)
  }

  val benchmarks = List(
    "puppet-bind" -> ("src/tests/server.pp", Some("src/modules")),
    "puppet-git" -> ("src/tests/init.pp", Some("src/modules")),
    "puppet-mosh" -> ("src/tests/init.pp", Some("src/modules")),
    "vagrant-cakephp" -> ("src/manifests/site.pp", Some("src/modules")),
    "vagrantpress" -> ("src/manifests/site.pp", Some("src/modules"))
    ).map(fixPaths)
     .toMap
     .mapValues(loadBenchmark)

}
