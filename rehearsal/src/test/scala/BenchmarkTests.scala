
class BenchmarkTests extends org.scalatest.FunSuite {

  import rehearsal._
  import puppet.Facter

  private val facterEnv = Facter.run() getOrElse
    (throw new Exception("Facter environment required"))

  for ((name, b) <- BenchmarkLoader.benchmarks) {

    test(s"benchmark: $name") {
      val resourceGraph = b.toGraph(facterEnv).head._2
      val fileScriptGraph = Slicing.sliceGraph(toFileScriptGraph(resourceGraph))
      info(fileScriptGraph.toString)
      assert(SymbolicEvaluator2.isDeterministic(fileScriptGraph))
    }
  }
}
