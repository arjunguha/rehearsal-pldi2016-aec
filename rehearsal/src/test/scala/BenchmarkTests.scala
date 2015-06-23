import rehearsal.fsmodel._
import rehearsal.ppmodel._
import puppet.Facter

import org.scalatest.FunSuite

class BenchmarkTests extends FunSuite {

  private val facterEnv = Facter.run() getOrElse
    (throw new Exception("Facter environment required"))

  for ((name, b) <- BenchmarkLoader.benchmarks) {

    test(s"benchmark: $name") {
      val resourceGraph = b.toGraph(facterEnv).head._2
      val fileScriptGraph = Slicing.sliceGraph(toFileScriptGraph(resourceGraph))
      info(fileScriptGraph.toString)
      assert(exp.SymbolicEvaluator2.isDeterministic(fileScriptGraph))
    }
  }
}
