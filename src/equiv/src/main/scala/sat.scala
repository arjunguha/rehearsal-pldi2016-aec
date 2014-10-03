package equiv.sat

import z3.scala._
import z3.scala.dsl._

import java.nio.file.{Paths, Path}

object Z3Puppet {

  private  implicit val z3 = new Z3Context(new Z3Config("MODEL" -> true))

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


  // z3 func declares in our model
  val (errSymbol, err) = mkZ3Func("err", Seq(), sSort)
  val (seqSymbol, seq) = mkZ3Func("seq", Seq(sSort, sSort), sSort)
  val (ancSymbol, is_ancestor) = mkZ3Func("is-ancestor", Seq(pathSort, pathSort), z3.mkBoolSort)
  val (dirnameSymbol, dirname) = mkZ3Func("dirname", Seq(pathSort, pathSort), z3.mkBoolSort)
  val (mkdirSymbol, mkdir) = mkZ3Func("mkdir", Seq(pathSort), sSort)
  val (rmdirSymbol, rmdir) = mkZ3Func("rmdir", Seq(pathSort), sSort)
  val (createSymbol, create) = mkZ3Func("create", Seq(pathSort), sSort)
  val (deleteSymbol, delete) = mkZ3Func("create", Seq(pathSort), sSort)
  val (shellSymbol, shell) = mkZ3Func("shell", Seq(pathSort), sSort)

  private val rootPathSymbol = z3.mkStringSymbol("root")
  private val root = z3.mkConst(rootPathSymbol, pathSort)


  //one transitive step
  private def addTransitive[A, B](s: Set[(A, B)]) = {
    s ++ (for ((x1, y1) <- s; (x2, y2) <- s if y1 == x2) yield (x1, y2))
  }

  //repeat until we don't get a bigger set
  private def transitiveClosure[A,B](s:Set[(A,B)]):Set[(A,B)] = {
    val t = addTransitive(s)
    if (t.size == s.size) s else transitiveClosure(t)
  }

  /*
  private def reflexiveClosure[A, B](s:Set[(A,B)]):Set[(A,B)] = {
    s ++ (for ((x, y) <- s) yield Set((x, x), (y,y)))
  }
  */

  // '/a' -> a ...
  private val pathMap = collection.mutable.Map[java.nio.file.Path, Z3AST]()

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
  private def dirnameofpath(path: Path): Set[(Path, Path)] = {
    if (null == path.getParent) {
      Set.empty
    }
    else {
      val t = Set[(Path, Path)]()
      val parent = path.getParent

      if (!pathMap.get(parent).isDefined) {
        val newast = z3.mkConst(parent.toString, pathSort)
        pathMap += ((parent, newast))
      }

      t ++ (parent, path)
      t ++ dirnameofpath(parent)
    }
  }

  private def dirnameRelation(): Set[(Path, Path)] = {
    val paths = pathMap.keySet
    val s = Set[(Path, Path)]()
    s ++ (for (path <- paths) yield dirnameofpath(path)).flatten
  }

  private def dirnameaxiomtree(relation: Set[(Path, Path)], p1: Z3AST, p2: Z3AST): Z3AST = {
    (dirname(p1, p2) --> (relation.map ({ case (l, r) => p1 === pathMap(l) && p2 == pathMap(r) })
                                  .foldLeft(false)({ case (acc, elem) => acc || elem })))
  }

  private def isAncestorAxiomTree(relation: Set[(Path, Path)], p1: Z3AST, p2: Z3AST): Z3AST = {
    val condexpr = relation.map({ case (parent, child) => (p1 === pathMap(parent) && p2 === pathMap(child)) })
                           .foldLeft(false)({case (acc, elem) => acc || elem })
    (is_ancestor(p1, p2) --> (p1 === p2) || condexpr)
  }

  def check() {
    val dirnamerelation = dirnameRelation()
    val isancestorrelation = transitiveClosure(dirnamerelation)

    val p1 = z3.mkBound(0, pathSort)
    val p2 = z3.mkBound(1, pathSort)
    val dirnamepattern = z3.mkPattern(dirname(p1 , p2)) // Not sure
    val dirnameAxiom = dirnameaxiomtree(dirnamerelation, p1, p2)

    val p1Symbol = z3.mkStringSymbol("p1")
    val p2Symbol = z3.mkStringSymbol("p2")
    val dirnamedefn = z3.mkForAll(0, List(dirnamepattern), List((p1Symbol, pathSort), (p2Symbol, pathSort)), dirnameAxiom)

    val isancestorpattern = z3.mkPattern(is_ancestor(p1, p2))
    val isancestorAxiom = isAncestorAxiomTree(isancestorrelation, p1, p2)
    val isancestordefn = z3.mkForAll(0, List(isancestorpattern), List((p1Symbol, pathSort), (p2Symbol, pathSort)), isancestorAxiom)

    val solver = z3.mkSolver
    solver.assertCnstr(dirnamedefn)
    solver.assertCnstr(isancestordefn)
  }
}
  
