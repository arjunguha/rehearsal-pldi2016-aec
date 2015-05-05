import org.scalatest.FunSuite

import pipeline._
import puppet.syntax._
import puppet.graph._
import eval._

class WeakestPreconditionTests extends InlineTestSuite {

  def genericTestRunner(resourceGraph: ResourceGraph,
                        fileScriptGraph: FileScriptGraph): Unit = {
    val pre = WeakestPreconditions.wpGraph(fileScriptGraph, True)
    info (s"Predicate has size ${pre.size}")
  }

}
