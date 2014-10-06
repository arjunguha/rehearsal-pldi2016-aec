package equiv.sat

import z3.scala._
import z3.scala.dsl._

import java.nio.file.{Paths, Path}

class Z3Puppet {

  implicit val context = new Z3Context(new Z3Config("MODEL" -> true))
  private val z3 = context

  private def mkZ3Sort(name: String)
              (implicit z3: Z3Context): (Z3Symbol, Z3Sort) = {
    val symbol = z3.mkStringSymbol(name)
    (symbol, z3.mkUninterpretedSort(symbol))
  }

  def mkZ3Func(name: String, DomainSorts: Seq[Z3Sort], RangeSort: Z3Sort)
              (implicit z3: Z3Context): (Z3Symbol, Z3FuncDecl) = {
    val symbol = z3.mkStringSymbol(name)
    (symbol, z3.mkFuncDecl(symbol, DomainSorts, RangeSort))
  }

  // z3 sorts in our model
  val (pathSymbol, pathSort) = mkZ3Sort("Path")
  val (sSymbol, sSort) = mkZ3Sort("S")
  val (cmdSymbol, cmdSort) = mkZ3Sort("Cmd")

  /* val sortMap = Map(pathSymbol -> pathSort, sSymbol -> sSort) */

  // z3 func declares in our model
  val (errSymbol, err) = mkZ3Func("err", Seq(), sSort) // 0 in KAT
  val (idSymbol, id) = mkZ3Func("id", Seq(), sSort) // 1 in KAT

  val (seqSymbol, seq) = mkZ3Func("seq", Seq(sSort, sSort), sSort)
  val (unionSymbol, union) = mkZ3Func("union", Seq(z3.mkBoolSort, sSort, sSort), sSort)

  val (ancSymbol, is_ancestor) = mkZ3Func("is-ancestor", Seq(pathSort, pathSort), z3.mkBoolSort)
  val (dirnameSymbol, dirname) = mkZ3Func("dirname", Seq(pathSort, pathSort), z3.mkBoolSort)
  val (existsSymbol, pexists) = mkZ3Func("exists", Seq(pathSort), z3.mkBoolSort)
  val (isdirSymbol, isdir) = mkZ3Func("isdir", Seq(pathSort), z3.mkBoolSort)
  val (isregularfileSymbol, isregularfile) = mkZ3Func("isregularfile", Seq(pathSort), z3.mkBoolSort)
  val (islinkSymbol, islink) = mkZ3Func("islink", Seq(pathSort), z3.mkBoolSort)

  val (mkdirSymbol, mkdir) = mkZ3Func("mkdir", Seq(pathSort), sSort)
  val (rmdirSymbol, rmdir) = mkZ3Func("rmdir", Seq(pathSort), sSort)
  val (createSymbol, create) = mkZ3Func("create", Seq(pathSort), sSort)
  val (deleteSymbol, delete) = mkZ3Func("delete", Seq(pathSort), sSort)
  val (linkSymbol, link) = mkZ3Func("link", Seq(pathSort), sSort)
  val (unlinkSymbol, unlink) = mkZ3Func("unlink", Seq(pathSort), sSort)
  val (shellSymbol, shell) = mkZ3Func("shell", Seq(pathSort), sSort)

  /*
  val funcMap = Map(errSymbol -> err,
                    seqSymbol -> seq,
                    unionSymbol -> union,
                    ancSymbol -> is_ancestor,
                    dirnameSymbol -> dirname,
                    mkdirSymbol -> mkdir,
                    rmdirSymbol -> rmdir,
                    createSymbol -> create,
                    deleteSymbol -> delete,
                    shellSymbol -> shell,
                    idSymbol -> id)
  */

  private val rootPathSymbol = z3.mkStringSymbol("root")
  private val root = z3.mkConst(rootPathSymbol, pathSort)

  //one transitive step
  private def addTransitive[A](s: Set[(A, A)]) = {
    s ++ (for ((x1, y1) <- s; (x2, y2) <- s if y1 == x2) yield (x1, y2))
  }

  //repeat until we don't get a bigger set
  private def transitiveClosure[A](s:Set[(A,A)]):Set[(A,A)] = {
    val t = addTransitive(s)
    if (t.size == s.size) s else transitiveClosure(t)
  }

  // '/a' -> a ...
  private val pathMap = collection.mutable.Map[Path, Z3AST]((Paths.get("/"), root))

  def toZ3Path(p: Path): Z3AST = {
    val ast = pathMap.get(p)
    ast getOrElse {
      val newast = z3.mkConst(p.toString, pathSort)
      pathMap += ((p, newast))
      newast
    }
  }

  def toZ3Path(path: String): Z3AST = {
    val p = Paths.get(path).normalize()
    val ast = pathMap.get(p)
    ast getOrElse {
      val newast = z3.mkConst(p.toString, pathSort)
      pathMap += ((p, newast))
      newast
    }
  }

  def toZ3Cmd(cmd: String): Z3AST = {
    z3.mkConst(cmd, cmdSort)
  }

  // Define dir Name
  private def dirnameOfPath(path: Path): Set[(Path, Path)] = {
    if (null == path.getParent) {
      Set.empty
    }
    else {
      val t = Set[(Path, Path)]()
      val parent = path.getParent

      // if z3 ast of path does not exist then create it
      if (!pathMap.get(parent).isDefined) {
        val newast = z3.mkConst(parent.toString, pathSort)
        pathMap += ((parent, newast))
      }

      val s = t + ((parent, path))
      s ++ dirnameOfPath(parent)
    }
  }

  private def dirnameRelation(paths: Set[Path]): Set[(Path, Path)] = {
    (for (path <- paths) yield dirnameOfPath(path)).flatten
  }

  private def printRelation(relation: Set[(Path, Path)]) {
    for (elem <- relation) println(s"${elem._1.toString}, ${elem._2.toString}")
  }

  private def dirnameaxiomtree(relation: Set[(Path, Path)], p1: Z3AST, p2: Z3AST): Z3AST = {
    val condexpr = relation.map ({ case (parent, child) => ((p1 === pathMap(parent)) && (p2 == pathMap(child))) })
                                  .foldLeft(false: Operands.BoolOperand)({ case (acc, elem) => acc || elem })
    z3.mkImplies(dirname(p1, p2), condexpr.ast(z3))
  }

  private def isAncestorAxiomTree(relation: Set[(Path, Path)], p1: Z3AST, p2: Z3AST): Z3AST = {
    val condexpr = relation.map({ case (ancestor, child) => (p1 === pathMap(ancestor) && p2 === pathMap(child)) })
                           .foldLeft(false: Operands.BoolOperand)({case (acc: Operands.BoolOperand, elem) => acc || elem })
    z3.mkImplies(is_ancestor(p1, p2), ((p1 === p2) || condexpr).ast(z3))
  }

  def isSatisfiable(ast: Z3AST): Option[Boolean] = {
    val dirnamerelation = dirnameRelation(pathMap.keySet.toSet)
    val isAncestorRelation = transitiveClosure(dirnamerelation)

    val p1 = z3.mkBound(0, pathSort)
    val p2 = z3.mkBound(1, pathSort)

    val dirnameAxiom = dirnameaxiomtree(dirnamerelation, p1, p2)
    val isancestorAxiom = isAncestorAxiomTree(isAncestorRelation, p1, p2)


    val p1Symbol = z3.mkStringSymbol("p1")
    val p2Symbol = z3.mkStringSymbol("p2")

    val dirnameDefn = z3.mkForAll(0, List(), List((p1Symbol, pathSort), (p2Symbol, pathSort)), dirnameAxiom)
    val isancestorDefn = z3.mkForAll(0, List(), List((p1Symbol, pathSort), (p2Symbol, pathSort)), isancestorAxiom)

    val solver = z3.mkSolver

    solver.assertCnstr(dirnameDefn)
    solver.assertCnstr(isancestorDefn)


    val z3paths = pathMap.values.toSeq
    solver.assertCnstr(z3.mkDistinct(z3paths: _*))

    /**************************** seq op is associative *************************************/
    val sa = z3.mkBound(0, sSort)
    val sb = z3.mkBound(1, sSort)
    val sc = z3.mkBound(2, sSort)
    val assoc = z3.mkEq(seq(sa, seq (sb, sc)), seq(seq(sa, sb), sc))

    val saSymbol = z3.mkStringSymbol("sa")
    val sbSymbol = z3.mkStringSymbol("sb")
    val scSymbol = z3.mkStringSymbol("sc")
    val assoc_forall = z3.mkForAll(0, List(), List((saSymbol, sSort), (sbSymbol, sSort), (scSymbol, sSort)), assoc)
    solver.assertCnstr(assoc_forall)
    /**********************************************************************************/


    /**************************** mkdir is commutative ********************************/
    val mkdir_commute_axiom = z3.mkImplies((!is_ancestor(p1, p2) && !is_ancestor(p2, p1)).ast(z3),
                                           z3.mkEq(seq(mkdir(p1), mkdir(p2)), seq(mkdir(p2), mkdir(p1))))
    val mkdir_commute_forall = z3.mkForAll(0, List(), List((p1Symbol, pathSort), (p2Symbol, pathSort)), mkdir_commute_axiom)
    solver.assertCnstr(mkdir_commute_forall)
    /*********************************************************************************/

    /**************************** create is commutative ********************************/
    val create_commute_axiom = z3.mkImplies((!is_ancestor(p1, p2) && !is_ancestor(p2, p1)).ast(z3),
                                            z3.mkEq(seq(create(p1), create(p2)), seq(create(p2), create(p1))))
    val create_commute_forall = z3.mkForAll(0, List(), List((p1Symbol, pathSort), (p2Symbol, pathSort)), create_commute_axiom)
    solver.assertCnstr(create_commute_forall)
    /*********************************************************************************/

    solver.assertCnstr(ast)
    solver.checkAssumptions()
  }
}
