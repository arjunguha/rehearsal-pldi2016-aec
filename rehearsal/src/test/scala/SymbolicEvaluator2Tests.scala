
import rehearsal.fsmodel._
import java.nio.file.Paths

class SymbolicEvaluator2Tests extends org.scalatest.FunSuite {

  import exp.SymbolicEvaluator2.{predEquals, exprEquals}

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


  //  val example1 = {
//    import fsmodel._
//    (And(TestFileState(Paths.get("/usr"), IsFile),
//      TestFileState(Paths.get("/lib"), IsDir)))
//  }
//
//  val example2 = {
//    import fsmodel._
//    TestFileState(Paths.get("/usr"), IsFile)
//
//  }


}