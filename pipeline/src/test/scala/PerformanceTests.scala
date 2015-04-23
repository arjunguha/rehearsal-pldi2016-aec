import org.scalatest.FunSuite

import pipeline._
import eval._
import puppet.syntax._
import puppet.graph._
import puppet.Facter

class PerformanceTests extends FunSuite {

  val env = Facter.emptyEnv
  val fs = Ubuntu.fs

  val tests = collection.Seq("/pkgs.pp")

  for (manifest <- tests) {

    test(manifest) {
      val url = getClass.getResource(manifest)
      val path = url.getPath()
      val program = parse(load(path, None))
      val graph = program.desugar().toGraph(env).head._2
      // val expr = pipeline.resourceGraphToExpr(graph)
      // val finalStates = Ample.finalStates(fs, expr)
      val finalStates = AmpleGraph.finalStates(fs, graph)(pipeline.GraphResourceToExpr)
      assert(1 == finalStates.size)
    }
  }
}
