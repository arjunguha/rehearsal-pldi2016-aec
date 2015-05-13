import pipeline._
import eval._
import puppet.Facter

import org.scalatest.FunSuite

class BenchmarkTests extends FunSuite {

  private val facterEnv = Facter.run() getOrElse
    (throw new Exception("Facter environment required"))

  for ((name, b) <- BenchmarkLoader.benchmarks) {

    test(s"benchmark: $name") {
//      val expr = pipeline.resourceGraphToExpr(b.toGraph(facterEnv).head._2)
//      val finalStates = Ample.finalStates(Ubuntu.fs, expr)
      // val graph = b.toGraph(facterEnv).head._2
      // val finalStates = AmpleGraph.finalStates(Ubuntu.fs, graph)(pipeline.GraphResourceToExpr)
      // assert(1 == finalStates.size)
      val myBdd = bdd.Bdd[TestFileState]((x, y) => x < y)
      val resourceGraph = b.toGraph(facterEnv).head._2
      val fileScriptGraph = Slicing.sliceGraph(pipeline.toFileScriptGraph(resourceGraph))
      info(fileScriptGraph.toString)
      val pre = WeakestPreconditions.wpGraphBdd(myBdd)(fileScriptGraph, myBdd.bddTrue)
      assert(Z3Evaluator.isDeterministic(myBdd)(myBdd.bddTrue, fileScriptGraph))
    }
  }
}
