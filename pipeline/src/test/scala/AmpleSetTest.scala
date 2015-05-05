import org.scalatest.FunSuite

import pipeline._
import puppet.syntax._
import puppet.graph._
import eval._
import puppet.Facter

class AmpleSetTests extends InlineTestSuite {

  val fs = Ubuntu.lightweight_fs

  def genericTestRunner(resourceGraph: ResourceGraph,
                        fileScriptGraph: FileScriptGraph): Unit = {
    val finalStates = AmpleGraph.finalStates(fs, resourceGraph)(pipeline.GraphResourceToExpr)
    assert(1 == finalStates.size)

  }
}