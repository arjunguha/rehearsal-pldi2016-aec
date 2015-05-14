import pipeline._
import eval._
import puppet.Facter

import org.scalatest.FunSuite

class BenchmarkTests extends FunSuite {

  private val facterEnv = Facter.run() getOrElse
    (throw new Exception("Facter environment required"))

  for ((name, b) <- BenchmarkLoader.benchmarks) {

    test(s"benchmark: $name") {
      val myBdd = bdd.Bdd[TestFileState]((x, y) => x < y)
      val resourceGraph = b.toGraph(facterEnv).head._2
      val fileScriptGraph = Slicing.sliceGraph(pipeline.toFileScriptGraph(resourceGraph))
      info(fileScriptGraph.toString)
      val pre = WeakestPreconditions.wpGraphBdd(myBdd)(fileScriptGraph, myBdd.bddTrue)
      assert(Z3Evaluator.isDeterministic(myBdd)(myBdd.bddTrue, fileScriptGraph))
    }
  }
}
