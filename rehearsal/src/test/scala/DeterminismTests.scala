import scalax.collection.Graph
import scalax.collection.GraphEdge.DiEdge
import rehearsal.ppmodel._
import rehearsal.fsmodel._
import puppet.graph._
import puppet.Facter
import Implicits._

class DeterminismTestSuite extends InlineTestSuite {

  def myTestRunner(g: FileScriptGraph): Boolean = {
    //SymbolicEvaluator.isErrorFree(g)
    SymbolicEvaluator.isDeterministic(g, false)
  }

  def genericTestRunner(resourceGraph: ResourceGraph,
                        g: FileScriptGraph): Unit = {
    SymbolicEvaluator.isDeterministic(g)
  }

  test("trivial program with non-deterministic error") {
    assert(myTestRunner(Graph(Mkdir("/foo"),
                              Mkdir("/foo/bar"))) == false)
  }

  test("trivial program with non-deterministic output") {
    assert(myTestRunner(
           Graph(If(TestFileState("/foo", IsDir), Mkdir("/bar"), Skip),
                 Mkdir("/foo")))
           == false)
  }


  test("Trivial, long program (performance test)") {

    def genSeq(n: Int) : Expr = {
      if (n == 0) {
        Mkdir("/bar")
      }
      else {
        If(TestFileState("/foo", IsDir), Skip, Mkdir("/foo")) >> genSeq(n - 1)
      }
    }

    myTestRunner(Graph(genSeq(100)))
  }

  test("Trivial, long program with many files (performance test)") {
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

    myTestRunner(Graph(genSeq(100)))
  }

  test("Is a singleton graph deterministic") {
    import Implicits._
    myTestRunner(Graph(If(TestFileState("/foo", IsDir), Skip, Mkdir("/foo"))))
  }

  test("Two-node non-deterministic graph") {
    import Implicits._
    myTestRunner(Graph(Mkdir("/foo"),
      If(TestFileState("/foo", IsDir), Skip, Mkdir("/bar"))))
  }

}
