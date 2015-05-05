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
    println(pre)
    assert(Z3Evaluator.isDeterministic(pre, fileScriptGraph))
  }

  test("trivial program with non-deterministic error") {
    import scalax.collection.Graph
    import Implicits._
    val fileScriptGraph: FileScriptGraph = Graph(Mkdir("/foo"), Mkdir("/foo/bar"))
    val pre = WeakestPreconditions.wpGraph(fileScriptGraph, True)
    println("Trivial")
    println(pre)
    assert(Z3Evaluator.isDeterministic(pre, fileScriptGraph))
  }

}
