import org.scalatest.FunSuite

import pipeline._
import puppet.syntax._
import puppet.graph._
import eval._
import puppet.Facter
import z3analysis.Z3Evaluator

class DeterminismTestSuite extends InlineTestSuite {

  def genericTestRunner(resourceGraph: ResourceGraph,
                        fileScriptGraph: FileScriptGraph): Unit = {
    val pre = WeakestPreconditions.wpGraph(fileScriptGraph, True)
    Z3Evaluator.isDeterministic(fileScriptGraph)
  }

}
