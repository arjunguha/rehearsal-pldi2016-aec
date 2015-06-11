
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