import org.scalatest.FunSuite

import puppet.driver.{PuppetDriver => driver}

class BenchmarkPOWidthTestSuite extends FunSuite {

  case class Benchmark(mainFile: String, modulePath: Option[String] = None)

  val benchmarkroot = "../benchmarks"

  val benchmarks = Map("puppet-bind" -> Benchmark("src/tests/server.pp", Some("src/modules")),
                       "puppet-git" -> Benchmark("src/tests/init.pp", Some("src/modules")),
                       "puppet-mosh" -> Benchmark("src/tests/init.pp", Some("src/modules")),
                       "vagrant-cakephp" -> Benchmark("src/manifests/site.pp",
                                                    Some("src/modules")),
                       "vagrantpress" -> Benchmark("src/manifests/site.pp",
                                                 Some("src/modules"))
                       )

  for ((name, b) <- benchmarks) {

    // XXX: Not a strict test, more like visual inspection
    test(s"benchmark: $name") {
      val mainFilePath = s"${benchmarkroot}/${name}/${b.mainFile}"
      val modulePath = b.modulePath.map((p) => s"${benchmarkroot}/${name}/${p}")

      val content = driver.prepareContent(mainFilePath, modulePath)
      val graph = driver.compile(content)
      println(s"Partial order with for benchmark ${name}, with #${graph.nodes.size} resources is: ${PartialOrderGlue.POWidth(graph)}")
    }
  }
}
