package equiv.sat

import z3.scala._
import z3.scala.dsl._

import java.nio.file.{Paths, Path}

class Z3Puppet {

  private implicit val z3 = new Z3Context(new Z3Config("MODEL" -> true))

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

  val sortMap = Map(pathSymbol -> pathSort, sSymbol -> sSort)

  // z3 func declares in our model
  val (errSymbol, err) = mkZ3Func("err", Seq(), sSort)
  val (seqSymbol, seq) = mkZ3Func("seq", Seq(sSort, sSort), sSort)
  val (ancSymbol, is_ancestor) = mkZ3Func("is-ancestor", Seq(pathSort, pathSort), z3.mkBoolSort)
  val (dirnameSymbol, dirname) = mkZ3Func("dirname", Seq(pathSort, pathSort), z3.mkBoolSort)
  val (mkdirSymbol, mkdir) = mkZ3Func("mkdir", Seq(pathSort), sSort)
  val (rmdirSymbol, rmdir) = mkZ3Func("rmdir", Seq(pathSort), sSort)
  val (createSymbol, create) = mkZ3Func("create", Seq(pathSort), sSort)
  val (deleteSymbol, delete) = mkZ3Func("delete", Seq(pathSort), sSort)
  val (shellSymbol, shell) = mkZ3Func("shell", Seq(pathSort), sSort)
  val (idSymbol, id) = mkZ3Func("id", Seq(pathSort), sSort)

  val funcMap = Map(errSymbol -> err,
                    seqSymbol -> seq,
                    ancSymbol -> is_ancestor,
                    dirnameSymbol -> dirname,
                    mkdirSymbol -> mkdir,
                    rmdirSymbol -> rmdir,
                    createSymbol -> create,
                    deleteSymbol -> delete,
                    shellSymbol -> shell,
                    idSymbol -> id)

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

  def toZ3Path(path: String): Z3AST = {
    val p = Paths.get(path).normalize()
    val ast = pathMap.get(p)
    ast getOrElse {
      val newast = z3.mkConst(p.toString, pathSort)
      pathMap += ((p, newast))
      newast
    }
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
    val ast = z3.mkImplies(is_ancestor(p1, p2), ((p1 === p2) || condexpr).ast(z3))
    println(ast)
    ast
  }

  def isSatisfiable(ast: Z3AST): Option[Boolean] = {
    val dirnamerelation = dirnameRelation(pathMap.keySet.toSet)
    val isAncestorRelation = transitiveClosure(dirnamerelation)
    printRelation(dirnamerelation)
    println ("------------------------------------------")
    printRelation(isAncestorRelation)
    println ("------------------------------------------")

    val p1 = z3.mkBound(0, pathSort)
    val p2 = z3.mkBound(1, pathSort)
    val dirnamepattern = z3.mkPattern(dirname(p1 , p2)) // Not sure
    val dirnameAxiom = dirnameaxiomtree(dirnamerelation, p1, p2)

    val p1Symbol = z3.mkStringSymbol("p1")
    val p2Symbol = z3.mkStringSymbol("p2")
    val dirnameDefn = z3.mkForAll(0, List(dirnamepattern), List((p1Symbol, pathSort), (p2Symbol, pathSort)), dirnameAxiom)
    println(dirnameDefn)

    val p3 = z3.mkBound(0, pathSort)
    val p4 = z3.mkBound(1, pathSort)
    val isancestorpattern = z3.mkPattern(is_ancestor(p3, p4))
    val isancestorAxiom = isAncestorAxiomTree(isAncestorRelation, p3, p4)

    val p3Symbol = z3.mkStringSymbol("p3")
    val p4Symbol = z3.mkStringSymbol("p4")
    val isancestorDefn = z3.mkForAll(0, List(isancestorpattern), List((p3Symbol, pathSort), (p4Symbol, pathSort)), isancestorAxiom)
    println(isancestorDefn)

    

    assert(java.nio.file.Files.isRegularFile(java.nio.file.Paths.get("../smt/axioms.smt")))
    z3.parseSMTLIB2File("../smt/axioms.smt", sortMap, funcMap)

    val solver = z3.mkSolver

    val z3paths = pathMap.values.toSeq
    solver.assertCnstr(z3.mkDistinct(z3paths: _*))

    solver.assertCnstr(dirnameDefn)
    solver.assertCnstr(isancestorDefn)
    solver.assertCnstr(ast)
    val res = solver.checkAssumptions()
    println(solver.getModel())
    res
  }
}
