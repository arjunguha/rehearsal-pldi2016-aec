class WeakestPreconditionTests extends InlineTestSuite {

  import puppet.graph._
  import rehearsal._
  import FSSyntax._

  def genericTestRunner(resourceGraph: ResourceGraph,
                        fileScriptGraph: FileScriptGraph): Unit = {
    val myBdd = bdd.Bdd[TestFileState]((x, y) => x < y)
    val predBdd = WeakestPreconditions.wpGraphBdd(myBdd)(fileScriptGraph, myBdd.bddTrue)
    val pred = WeakestPreconditions.bddToPred(myBdd)(predBdd)
    info (s"Predicate has size ${pred.size} and cache has size ${myBdd.cacheSize}")
  }


}
