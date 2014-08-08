import org.scalatest.FunSuite

import puppet.driver.{PuppetDriver => driver}

class BenchmarkSuite extends FunSuite {

  case class Benchmark(mainFile: String, modulePath: Option[String] = None)

  val benchmarkroot = "../benchmarks"

  val benchmarks = Map("puppet-bind" -> Benchmark("src/tests/server.pp", Some("src/modules")),
                       "puppet-git" -> Benchmark("src/tests/init.pp", Some("src/modules")),
                       "puppet-mosh" -> Benchmark("src/tests/init.pp", Some("src/modules")),
                       "vagrant-cakephp" -> Benchmark("src/manifests/site.pp",
                                                    Some("src/modules")),
                       "vagrantpress" -> Benchmark("src/manifests/site.pp",
                                                 Some("src/modules"))
                       // TODO : Add more tests
                    /*"puppet-rbenv" -> Benchmark("src/tests/init.pp", Some("src/modules"))*/
                       )

  for ((name, b) <- benchmarks) {

    test (s"compiling benchmark: $name") {
      val mainFilePath = s"${benchmarkroot}/${name}/${b.mainFile}"
      val modulePath = b.modulePath.map((p) => s"${benchmarkroot}/${name}/${p}")
      val content = driver.prepareContent(mainFilePath, modulePath)
      val graph = driver.compile(content)
    }
  }

  val dockerBenchmarks = List("puppet-git", "puppet-mosh", "puppet-bind")

  dockerBenchmarks foreach ((name) => {
    val b = benchmarks(name)

    test (s"running benchmark: $name") {
      val mainFilePath = s"${benchmarkroot}/${name}/${b.mainFile}"
      val modulePath = b.modulePath.map((p) => s"${benchmarkroot}/${name}/${p}")
      val content = driver.prepareContent(mainFilePath, modulePath)
      val graph = driver.compile(content)
      driver.verify(graph)
    }
  })
}
