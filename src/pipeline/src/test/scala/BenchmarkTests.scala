package pipeline

import org.scalatest.FunSuite

class BenchmarkTests extends FunSuite {

  val benchmarkroot = "../benchmarks"

  val benchmarks = Map("puppet-bind" -> ("src/tests/server.pp", Some("src/modules")),
                       "puppet-git" -> ("src/tests/init.pp", Some("src/modules")),
                       "puppet-mosh" -> ("src/tests/init.pp", Some("src/modules")),
                       "vagrant-cakephp" -> ("src/manifests/site.pp", Some("src/modules"))
                       // "vagrantpress" -> ("src/manifests/site.pp", Some("src/modules"))
                       )

  for ((name, b) <- benchmarks) {

    test(s"benchmark: $name") {
      val mainFilePath = s"${benchmarkroot}/${name}/${b._1}"
      val modulePath = b._2.map((p) => s"${benchmarkroot}/${name}/${p}")

      assert(1 == pipeline.run(mainFilePath, modulePath, Ubuntu.fs))
    }
  }
}
