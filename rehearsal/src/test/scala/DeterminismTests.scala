import scalax.collection.Graph
import scalax.collection.GraphEdge.DiEdge
import rehearsal.ppmodel._
import rehearsal.fsmodel._
import puppet.syntax.parse
import puppet.graph._
import puppet.Facter
import Implicits._

class DeterminismTestSuite extends /*InlineTestSuite*/ org.scalatest.FunSuite {

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

    myTestRunner(Graph(genSeq(10)))
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

    myTestRunner(Graph(genSeq(10)))
  }

  test("Is a singleton graph deterministic") {
    import Implicits._
    myTestRunner(Graph(If(TestFileState("/foo", IsDir), Skip, Mkdir("/foo"))))
  }

  test("Two-node non-deterministic graph") {
    import Implicits._
    assert(false == myTestRunner(Graph(Mkdir("/foo"),
      If(TestFileState("/foo", IsDir), Skip, Mkdir("/bar")))))
  }

  test("a bug") {
    val p = "/usr/games/sl"
    val c = ""
    val n1 = CreateFile(p, c)
    val n2 = If(TestFileState(p, IsFile),
                Rm(p) >> CreateFile(p, c),
                If(TestFileState(p, DoesNotExist), CreateFile(p, c), Skip))
    assert(false == myTestRunner(Graph(n1, n2)))
  }

  test("should be deterministic") {
    val p = "/usr/foo"
    val c = "c"
    assert(true == myTestRunner(Graph(CreateFile(p, c), CreateFile(p, c))))
  }

  test("file removal and creation should be non-deterministic") {
    val p = "/usr/foo"
    assert(false == myTestRunner(Graph(Rm(p), CreateFile(p, ""))))
  }

  test("package with config file non-deterministic graph") {
    val program = """
      file {'/usr/games/sl': ensure => present }

      package {'sl': ensure => present }
    """
    val pp = parse(program)
    val g = toFileScriptGraph(pp.desugar.toGraph(Facter.emptyEnv).head._2)
    //g.nodes.foreach(n => println(n.value.pretty()))
    val g2 = Slicing.sliceGraph(g)
    //g2.nodes.foreach(n => println(n.value.pretty()))
    assert(false == myTestRunner(g))
  }

  test("should be non-deterministic") {
    val p = "/usr/foo"
    val c1 = "contents 1"
    val c2 = "contents 2"
    val stmt1 = If(TestFileState(p, DoesNotExist), CreateFile(p, c1), Rm(p) >> CreateFile(p, c1))
    val stmt2 = If(TestFileState(p, DoesNotExist), CreateFile(p, c2), Rm(p) >> CreateFile(p, c2))
    assert(false == myTestRunner(Graph(stmt1, stmt2)))
  }


}
