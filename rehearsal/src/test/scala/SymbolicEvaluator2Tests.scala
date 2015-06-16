
import rehearsal.fsmodel._
import java.nio.file.Paths
import scalax.collection.Graph
import scalax.collection.GraphEdge.DiEdge
import rehearsal.ppmodel._
import puppet.syntax.parse
import puppet.graph._
import puppet.Facter
import rehearsal.fsmodel.Implicits._

class SymbolicEvaluator2Tests extends org.scalatest.FunSuite {

  import exp.SymbolicEvaluator2.{predEquals, exprEquals, isDeterministic}

  test("simple equality") {
    val x = TestFileState(Paths.get("/usr"), IsFile)
    assert(predEquals(x, x))
  }

  test("basic predicates") {
    val x = TestFileState(Paths.get("/usr"), IsFile)
    val y = TestFileState(Paths.get("/usr"), IsDir)
    assert(predEquals(x, y) == false)
  }

  test("program equivalence") {
    val x = CreateFile(Paths.get("/usr"), Array.fill(16)(0))
    assert(exprEquals(x, x))
  }


  test("program equivalence 2") {
    val x = CreateFile(Paths.get("/usr"), Array.fill(16)(0))
    val y = CreateFile(Paths.get("/lib"), Array.fill(16)(0))
    assert(exprEquals(Seq(x, y), Seq(y, x)))
  }

  test("program equivalence 3") {
    val x = CreateFile(Paths.get("/usr/bin"), Array.fill(16)(0))
    val y = CreateFile(Paths.get("/usr"), Array.fill(16)(0))
    assert(exprEquals(x, y) == false)
  }

  test("program equivalence 4 - Mkdir"){
    val x = Mkdir(Paths.get("/usr"))
    assert(exprEquals(x, x))
  }

  test("program equivalence 5 - Mkdir") {
    val x = Mkdir(Paths.get("/usr"))
    val y = CreateFile(Paths.get("/usr/bin"), Array.fill(16)(0))
    assert(exprEquals(Seq(x, y), Seq(y, x)) == false)
  }

  test("program equivalence 6 - Mkdir"){
    val x = Mkdir(Paths.get("/usr"))
    val y = Mkdir(Paths.get("/lib"))
    assert(exprEquals(Seq(x, y), Seq(y, x)))
  }

  test("program equivalence 7 - Rm"){
    val y = CreateFile(Paths.get("/usr"), Array.fill(16)(0))
    val x = Rm(Paths.get("/usr"))
    assert(exprEquals(Seq(y, x), Seq(x, y)) == false)
  }

  test("program equivalence 8 - Rm"){
    val x = CreateFile(Paths.get("/usr"), Array.fill(16)(0))
    val y = CreateFile(Paths.get("/lib"), Array.fill(16)(0))
    val x1 = Rm(Paths.get("/usr"))
    val y1 = Rm(Paths.get("/lib"))
    assert(exprEquals(Seq(Seq(x, y), Seq(x1, y1)),
                      Seq(Seq(x, y), Seq(y1, x1))))
  }

  test("program equivalence 9 - Cp"){
    val x = CreateFile(Paths.get("/usr"), Array.fill(16)(0))
    val y = Cp(Paths.get("/usr"), Paths.get("/lib"))
    val z = CreateFile(Paths.get("/lib"), Array.fill(16)(0))
    assert(exprEquals(Seq(x, y), Seq(x, z)))
  }

  test("trivial program with non-deterministic output") {
    val g = Graph[Expr, DiEdge](If(TestFileState(Paths.get("/foo"), IsDir), Mkdir(Paths.get("/bar")), Skip),
                                Mkdir(Paths.get("/foo")))

    assert(isDeterministic(g) == false)
  }

  test("trivial program with non-deterministic error"){
    val g = Graph[Expr, DiEdge](Mkdir("/foo"), Mkdir("/foo/bar"))
    assert(isDeterministic(g) == false)
  }

  test("Is a singleton graph deterministic") {
    isDeterministic(Graph[Expr, DiEdge](If(TestFileState(Paths.get("/foo"), IsDir), Skip,
                                        Mkdir(Paths.get("/foo")))))
  }

  test("Two-node non-deterministic graph") {
    assert(false == isDeterministic(Graph[Expr, DiEdge](Mkdir(Paths.get("/foo")),
      If(TestFileState(Paths.get("/foo"), IsDir), Skip, Mkdir(Paths.get("/bar"))))))
  }

  test("a bug") {
    val p = Paths.get("/usr/games/sl")
    val c = ""
    val n1 = CreateFile(p, c)
    val n2 = If(TestFileState(p, IsFile),
      Rm(p) >> CreateFile(p, c),
      If(TestFileState(p, DoesNotExist), CreateFile(p, c), Skip))
    assert(false == isDeterministic(Graph[Expr, DiEdge](n1, n2)))
  }

  test("should be deterministic") {
    val p = Paths.get("/usr/foo")
    val c = "c"
    assert(true == isDeterministic(Graph[Expr, DiEdge](CreateFile(p, c), CreateFile(p, c))))
  }

  test("file removal and creation should be non-deterministic") {
    val p = Paths.get("/usr/foo")
    assert(false == isDeterministic(Graph[Expr, DiEdge](Rm(p), CreateFile(p, ""))))
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
    assert(false == isDeterministic(g))
  }

  test("should be non-deterministic") {
    info("Should work")
    val p = Paths.get("/usr/foo")
    val c1 = "contents 1"
    val c2 = "contents 2"
    val stmt1 = If(TestFileState(p, DoesNotExist), CreateFile(p, c1), Rm(p) >> CreateFile(p, c1))
    val stmt2 = If(TestFileState(p, DoesNotExist), CreateFile(p, c2), Rm(p) >> CreateFile(p, c2))
    assert(false == isDeterministic(Graph[Expr, DiEdge](stmt1, stmt2)))
  }

//    val example1 = {
//    import rehearsal.fsmodel._
//    (And(TestFileState(Paths.get("/usr"), IsFile),
//      TestFileState(Paths.get("/lib"), IsDir)))
//  }
//
//  val example2 = {
//    import rehearsal.fsmodel._
//    TestFileState(Paths.get("/usr"), IsFile)
//
//  }


}