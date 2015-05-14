import org.scalatest.FunSuite

import scalax.collection.Graph
import scalax.collection.GraphEdge.DiEdge
import pipeline._
import puppet.graph._
import eval._
import puppet.Facter

class DeterminismTestSuite extends InlineTestSuite {

  def genericTestRunner(resourceGraph: ResourceGraph,
                        g: FileScriptGraph): Unit = {
    val myBdd = bdd.Bdd[TestFileState]((x, y) => x < y)
    val fileScriptGraph = Slicing.sliceGraph(g)
    println(fileScriptGraph)
    val pre = WeakestPreconditions.wpGraphBdd(myBdd)(fileScriptGraph, myBdd.bddTrue)
    println(WeakestPreconditions.bddToPred(myBdd)(pre))
    assert(Z3Evaluator.isDeterministic(myBdd)(pre, fileScriptGraph))
  }

  test("trivial program with non-deterministic error") {
    import scalax.collection.Graph
    import Implicits._
    val fileScriptGraph: FileScriptGraph = Graph(Mkdir("/foo"), Mkdir("/foo/bar"))
    val myBdd = bdd.Bdd[TestFileState]((x, y) => x < y)
    val pre = WeakestPreconditions.wpGraphBdd(myBdd)(fileScriptGraph, myBdd.bddTrue)
    println(WeakestPreconditions.bddToPred(myBdd)(pre))
    assert(Z3Evaluator.isDeterministic(myBdd)(pre, fileScriptGraph) == false)
  }

  test("trivial program with non-deterministic output") {
    import scalax.collection.Graph
    import Implicits._
    val fileScriptGraph: FileScriptGraph = Graph(
      If(TestFileState("/foo", IsDir), Mkdir("/bar"), Skip),
      Mkdir("/foo"))
    val myBdd = bdd.Bdd[TestFileState]((x, y) => x < y)
    val pre = WeakestPreconditions.wpGraphBdd(myBdd)(fileScriptGraph, myBdd.bddTrue)
    assert(Z3Evaluator.isDeterministic(myBdd)(pre, fileScriptGraph) == false)
  }


  test("Trivial, long program (performance test)") {
    import scalax.collection.Graph
    import Implicits._

    def genSeq(n: Int) : Expr = {
      import Implicits._
      if (n == 0) {
        Mkdir("/bar")
      }
      else {
        If(TestFileState("/foo", IsDir), Skip, Mkdir("/foo")) >> genSeq(n - 1)
      }
    }

    val fileScriptGraph: FileScriptGraph = Graph(
      genSeq(1000))
    val myBdd = bdd.Bdd[TestFileState]((x, y) => x < y)
    val pre = WeakestPreconditions.wpGraphBdd(myBdd)(fileScriptGraph, myBdd.bddTrue)
    assert(Z3Evaluator.isDeterministic(myBdd)(pre, fileScriptGraph) == true)
  }

  test("Trivial, long program with many files (performance test)") {
    import scalax.collection.Graph
    import Implicits._

    def genSeq(n: Int) : Expr = {
      import Implicits._
      if (n == 0) {
        Mkdir("/bar")
      }
      else {
        Mkdir(s"/$n") >> genSeq(n - 1)
      }
    }

    val fileScriptGraph: FileScriptGraph = Graph(genSeq(100))
    val myBdd = bdd.Bdd[TestFileState]((x, y) => x < y)
    val pre = WeakestPreconditions.wpGraphBdd(myBdd)(fileScriptGraph, myBdd.bddTrue)
    assert(Z3Evaluator.isDeterministic(myBdd)(pre, fileScriptGraph) == true)
  }

  test("Is a singleton graph deterministic") {
    import Implicits._
    val myBdd = bdd.Bdd[TestFileState]((x, y) => x < y)
    val g = Graph[Expr, DiEdge](If(TestFileState("/foo", IsDir), Skip, Mkdir("/foo")))
    assert(Z3Evaluator.isDeterministic(myBdd)(myBdd.bddTrue, g))
  }

  test("Two-node non-deterministic graph") {
    import Implicits._
    val myBdd = bdd.Bdd[TestFileState]((x, y) => x < y)

    val g = Graph[Expr, DiEdge](
      Mkdir("/foo"),
      If(TestFileState("/foo", IsDir), Skip, Mkdir("/bar")))
    assert(Z3Evaluator.isDeterministic(myBdd)(myBdd.bddTrue, g) == false)
  }

}
