import equiv.ast._

import org.scalatest.{FunSuite, Matchers}

class Core extends FunSuite with Matchers {
  import z3.scala._
  import z3.scala.dsl._

  import equiv.sat._

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

    val sa = z3.mkBound(0, sSort)
    val sb = z3.mkBound(1, sSort)
    val sc = z3.mkBound(2, sSort)
    val assoc = z3.mkEq(seq(sa, seq (sb, sc)), seq(seq(sa, sb), sc))

    val saSymbol = z3.mkStringSymbol("sa")
    val sbSymbol = z3.mkStringSymbol("sb")
    val scSymbol = z3.mkStringSymbol("sc")
    val assoc_forall = z3.mkForAll(0, List(), List((saSymbol, sSort), (sbSymbol, sSort), (scSymbol, sSort)), assoc)

    // declare-consts
    val rootPathSymbol = z3.mkStringSymbol("root")
    val aPathSymbol = z3.mkStringSymbol("/a")
    val bPathSymbol = z3.mkStringSymbol("/b")
    val cPathSymbol = z3.mkStringSymbol("/c")
    val dPathSymbol = z3.mkStringSymbol("/d")

    val root = z3.mkConst(rootPathSymbol, pathSort)
    val a = z3.mkConst(aPathSymbol, pathSort)
    val b = z3.mkConst(bPathSymbol, pathSort)
    val c = z3.mkConst(cPathSymbol, pathSort)
    val d = z3.mkConst(dPathSymbol, pathSort)

    val distinct_axiom = z3.mkDistinct(root, a, b, c, d)

    /* forall ((p1 Path) (p2 Path))
     *   (= (is-ancestor p1 p2)
     *       (or (= p1 p2)
     *          (= root p2)
     *          (= a d)))
     */
    val p1 = z3.mkBound(0, pathSort)
    val p2 = z3.mkBound(1, pathSort)
    val axiomtree = z3.mkImplies(is_ancestor(p1, p2), ((p1 === p2) || (root === p2) ||  (a === d)).ast(z3))

    val p1Symbol: Z3Symbol = z3.mkStringSymbol("p1")
    val p2Symbol: Z3Symbol = z3.mkStringSymbol("p2")
    val is_ancestor_defn = z3.mkForAll(0, List(), List((p1Symbol, pathSort), (p2Symbol, pathSort)), axiomtree)


    val mkdir_commute = z3.mkImplies((!is_ancestor(p1, p2) && !is_ancestor(p2, p1)).ast(z3),
                                     z3.mkEq(seq(mkdir(p1), mkdir(p2)), seq(mkdir(p2), mkdir(p1))))
    val commute_forall = z3.mkForAll(0, List(), List((p1Symbol, pathSort), (p2Symbol, pathSort)), mkdir_commute)

    // Commutative
    val commute_axiom = ((seq(mkdir(a), mkdir(b))) !== (seq(mkdir(b),(mkdir(a)))))

    val solver = z3.mkSolver
    solver.assertCnstr(distinct_axiom)
    solver.assertCnstr(is_ancestor_defn)
    solver.assertCnstr(assoc_forall)
    solver.assertCnstr(commute_forall)
    solver.assertCnstr(commute_axiom)
    assert(solver.checkAssumptions() == Some(false))
  }

  test("mkdir-commutes") {
    val z3 = new Z3Puppet

    val p1 = "/b"
    val p2 = "/c"

    val z3p1 = z3.toZ3Path (p1)
    val z3p2 = z3.toZ3Path (p2)
    val mkdir = z3.mkdir
    val seq = z3.seq

    val commute_axiom = seq(mkdir(z3p1), mkdir(z3p2)) !== seq(mkdir(z3p2), mkdir(z3p1))

    assert(z3.isSatisfiable(commute_axiom) == Some(false))
  }

  test("mkdir commutes") {
    val e1 = Block(MkDir("/a"), MkDir("/b"))
    val e2 = Block(MkDir("/b"), MkDir("/a"))
    val z3 = new Z3Puppet()
    assert(Some(true) == z3.isEquiv(e1, e2))
  }

  test("mkdir commutes (2x associativity needed)") {
    val z3 = new Z3Puppet()
    val e1 = Block(MkDir("/a"), Block(MkDir("/b"), MkDir("/c")))
    val e2 = Block(Block(MkDir("/c"), MkDir("/a")), MkDir("/b"))
    assert(Some(true) == z3.isEquiv(e1, e2))
  }

  test("mkdir commutes (3x associativity needed)") {
    val z3 = new Z3Puppet()
    val e1 = Block(MkDir("/a"), Block(MkDir("/c"), MkDir("/b")))
    val e2 = Block(Block(MkDir("/c"), MkDir("/a")), MkDir("/b"))
    assert(Some(true) == z3.isEquiv(e1, e2))
  }


}
