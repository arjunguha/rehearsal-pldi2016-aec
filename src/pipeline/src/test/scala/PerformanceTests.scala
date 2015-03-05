package pipeline

import org.scalatest.FunSuite

class PerformanceTests extends FunSuite {

  val env = Facter.emptyEnv
  val fs = Ubuntu.fs

  val tests = Seq("/pkgs.pp")

  for (manifest <- tests) {

    test(manifest) {
      val url = getClass.getResource(manifest)
      val path = url.getPath()
      assert(1 == pipeline.run(path, None, env, fs))
    }
  }
}



