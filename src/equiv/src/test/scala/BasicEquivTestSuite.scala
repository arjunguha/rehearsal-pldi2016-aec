
import org.scalatest.{FunSuite, Matchers}

class Core extends FunSuite with Matchers {
  import z3.scala._
  import z3.scala.dsl._

  def mkZ3Sort(name: String)
              (implicit z3: Z3Context): (Z3Symbol, Z3Sort) = {
    val symbol = z3.mkStringSymbol(name)
    (symbol, z3.mkUninterpretedSort(symbol))
  }

  def mkZ3Func(name: String, DomainSorts: Seq[Z3Sort], RangeSort: Z3Sort)
              (implicit z3: Z3Context): (Z3Symbol, Z3FuncDecl) = {
    val symbol = z3.mkStringSymbol(name)
    (symbol, z3.mkFuncDecl(symbol, DomainSorts, RangeSort))
  }
              

  test("Core") {
    implicit val z3 = new Z3Context(new Z3Config("MODEL" -> true))

    val (pathSymbol, pathSort) = mkZ3Sort("Path")
    val (sSymbol, sSort) = mkZ3Sort("S")
 
    val (errSymbol, err) = mkZ3Func("err", Seq(), sSort)
    val (seqSymbol, seq) = mkZ3Func("seq", Seq(sSort, sSort), sSort)
    val (ancSymbol, is_ancestor) = mkZ3Func("is-ancestor", Seq(pathSort, pathSort), z3.mkBoolSort)
    val (mkdirSymbol, mkdir) = mkZ3Func("mkdir", Seq(pathSort), sSort)
    val (createSymbol, create) = mkZ3Func("create", Seq(pathSort), sSort)

    val sortMap = Map(pathSymbol -> pathSort, sSymbol -> sSort)
    val funcMap = Map(errSymbol -> err, seqSymbol -> seq,
                      ancSymbol -> is_ancestor, mkdirSymbol -> mkdir,
                      createSymbol -> create)

    assert(java.nio.file.Files.isRegularFile(java.nio.file.Paths.get("../smt/axioms.smt")))
    z3.parseSMTLIB2File("../smt/axioms.smt", sortMap, funcMap)

    // declare-consts
    val rootPathSymbol = z3.mkStringSymbol("root")
    val aPathSymbol = z3.mkStringSymbol("a")
    val bPathSymbol = z3.mkStringSymbol("b")
    val cPathSymbol = z3.mkStringSymbol("c")
    val dPathSymbol = z3.mkStringSymbol("d")

    val root = z3.mkConst(rootPathSymbol, pathSort)
    val a = z3.mkConst(aPathSymbol, pathSort)
    val b = z3.mkConst(bPathSymbol, pathSort)
    val c = z3.mkConst(cPathSymbol, pathSort)
    val d = z3.mkConst(dPathSymbol, pathSort)


    /* forall ((p1 Path) (p2 Path))
     *   (= (is-ancestor p1 p2)
     *       (or (= p1 p2)
     *          (= root p2)
     *          (= a d)))
     */
    val p1 = z3.mkBound(0, pathSort)
    val p2 = z3.mkBound(1, pathSort)
    val pattern = z3.mkPattern(is_ancestor(p1 , p2)) // Not sure
    val axiomtree = (is_ancestor(p1, p2) --> (p1 === p2) || (root === p2) ||  (a === d))

    val p1Symbol: Z3Symbol = z3.mkStringSymbol("p1")
    val p2Symbol: Z3Symbol = z3.mkStringSymbol("p2")
    val is_ancestor_defn = z3.mkForAll(0, List(pattern), List((p1Symbol, pathSort), (p2Symbol, pathSort)), axiomtree)

    // Commutative
    val commute_axiom = ((seq(mkdir(a), mkdir(b))) !== (seq(mkdir(a),(mkdir(b)))))

    val solver = z3.mkSolver

    solver.assertCnstr(is_ancestor_defn)
    solver.assertCnstr(commute_axiom)
    println(solver.checkAssumptions())
    // println(solver.getModel())
    // solver.assertCnstr(p2 --> !(y === zero))
    // solver.assertCnstr(p3 --> !(x === zero))

    // solver.checkAssumptions(p1, p2, p3) match {

    // result should equal (Some(false))
    // core.toSet should equal (Set(p1, p3))
  }
}

