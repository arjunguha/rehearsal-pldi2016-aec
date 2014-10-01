
import org.scalatest.{FunSuite, Matchers}

class Core extends FunSuite with Matchers {
  import z3.scala._
  import z3.scala.dsl._

  test("Core") {
    val z3 = new Z3Context(new Z3Config("MODEL" -> true))

    val pathSymbol = z3.mkStringSymbol("Path")
    val Z3Path = z3.mkUninterpretedSort(pathSymbol)
    // val x = z3.mkStringSymbol("x")
    // val x = z3.mkFreshConst("x", z3.mkBoolSort)
    // val y = z3.mkFreshConst("y", z3.mkBoolSort)


    assert(java.nio.file.Files.isRegularFile(java.nio.file.Paths.get("../smt/axioms.smt")))
    val ast = z3.parseSMTLIB2File("../smt/axioms.smt", Map(pathSymbol -> Z3Path), Map.empty)

//    println (z3.getASTKind(ast));

//    println(z3.astToString(ast));

    // val x = 
    // val y = 

//    println("working")



    val solver = z3.mkSolver
    // val expr = (x !== y)
    //solver.assertCnstr(expr.ast(z3))
    // solver.assertCnstr(expr)
    println(solver.checkAssumptions())
    println(solver.getModel())
    // solver.assertCnstr(p2 --> !(y === zero))
    // solver.assertCnstr(p3 --> !(x === zero))

    // solver.checkAssumptions(p1, p2, p3) match {

    // result should equal (Some(false))
    // core.toSet should equal (Set(p1, p3))
  }
}

