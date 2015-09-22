object BenchmarkLoader {

  import rehearsal._

  private val facterEnv = Map()

  // TODO(arjun): Should be in scala-puppet
  private def loadBenchmark(bench: (String, String)): puppet.core.BlockStmtC = {
    val (mainFile, modulePath) = bench
    puppet.syntax.parse(puppet.syntax.load(mainFile, modulePath)).desugar()
  }

  private def fixPaths(benchWithName: ((String, (String, String)))) = {
    val (name, (mainFile, modulePath)) = benchWithName
    val mainFileFixed = s"benchmarks/$name/$mainFile"
    val modulePathFixed = "benchmarks/$name/$modulePath"
    name -> (mainFileFixed -> modulePathFixed)
  }

  val benchmarks = List(
    "puppet-bind" -> ("src/tests/server.pp", "src/modules"),
    "puppet-git" -> ("src/tests/init.pp", "src/modules"),
    "puppet-mosh" -> ("src/tests/init.pp", "src/modules"),
    "vagrant-cakephp" -> ("src/manifests/site.pp", "src/modules"),
    "vagrantpress" -> ("src/manifests/site.pp", "src/modules")
    ).map(fixPaths)
     .toMap
     .mapValues(loadBenchmark)

}
