package equiv.sat 

import equiv.desugar._
import equiv.ast

import z3.scala._
import z3.scala.dsl._
import z3.scala.dsl.Operands._

import java.nio.file.{Paths, Path}

class Z3Puppet {
  
  import equiv.desugar.Desugar._

  implicit val context = new Z3Context(new Z3Config("MODEL" -> true, "TIMEOUT" -> 3000))
  private val z3 = context

  // z3 sorts in our model
  val pathSort = z3.mkUninterpretedSort("Path")
  val fsSort   = z3.mkUninterpretedSort("FS")
  val boolSort = z3.mkBoolSort

  val initfs = z3.mkConst("FSINIT", fsSort)
  val fserr  = z3.mkConst("FSERR", fsSort)

  val root = z3.mkConst("/", pathSort)

  val pexists = z3.mkFuncDecl("pexists", Seq(pathSort, fsSort), boolSort)
  val isdir   = z3.mkFuncDecl("isdir",   Seq(pathSort, fsSort), boolSort)
  val isfile  = z3.mkFuncDecl("isfile",  Seq(pathSort, fsSort), boolSort)
  val islink  = z3.mkFuncDecl("islink",  Seq(pathSort, fsSort), boolSort)

  private def ancestors(p: Path): Set[Path] = p.getParent match {
    case null => Set.empty
    case parent: Path => Set(p.normalize) ++ ancestors(parent)
  }

  private def gatherPaths(pr: ast.Predicate): Set[Path] = pr match {
    case ast.True => Set.empty
    case ast.False => Set.empty
    case ast.Exists(p) => ancestors(p)
    case ast.IsDir(p) => ancestors(p)
    case ast.IsRegularFile(p) => ancestors(p)
    case ast.IsLink(p) => ancestors(p)
    case ast.And(lhs, rhs) => gatherPaths(lhs) ++ gatherPaths(rhs)
    case ast.Or(lhs, rhs) => gatherPaths(lhs) ++ gatherPaths(rhs)
    case ast.Not(oper) => gatherPaths(oper)
  }

  private def gatherPaths(e: FSKATExpr): Set[Path] = e match {
    case Id => Set.empty
    case Err => Set.empty
    case MkDir(p) => ancestors(p)
    case RmDir(p) => ancestors(p)
    case Create(p) => ancestors(p)
    case Delete(p) => ancestors(p)
    case Link(p) => ancestors(p)
    case Unlink(p) => ancestors(p)
    case Shell(p) => ancestors(p)
    case Filter(pr) => gatherPaths(pr)
    case Seqn(lhs, rhs) => gatherPaths(lhs) ++ gatherPaths(rhs)
    case Opt(lhs, rhs) => gatherPaths(lhs) ++ gatherPaths(rhs)
  }

  private def toZ3AST(p: Path): Z3AST = z3.mkConst(p.toString, pathSort)

  private def predeval(pr: ast.Predicate, infs: Z3AST)
                      (implicit pathmap: Map[Path, Z3AST]): Z3AST = pr match {
    case ast.True => (true).ast(context)
    case ast.False => (false).ast(context)

    case ast.Exists(p) => {
      val z3path = pathmap.get(p) getOrElse (throw new Exception("path not mapped"))
      pexists(z3path, infs)
    }

    case ast.IsDir(p) => {
      val z3path = pathmap.get(p) getOrElse (throw new Exception("path not mapped"))
      isdir(z3path, infs)
    }

    case ast.IsRegularFile(p) => {
      val z3path = pathmap.get(p) getOrElse (throw new Exception("path not mapped"))
      isfile(z3path, infs)
    }

    case ast.IsLink(p) => {
      val z3path = pathmap.get(p) getOrElse (throw new Exception("path not mapped"))
      islink(z3path, infs)
    }

    case ast.And(lhs, rhs) => (predeval(lhs, infs) && predeval(rhs, infs)).ast(context)
    case ast.Or(lhs, rhs) => (predeval(lhs, infs) || predeval(rhs, infs)).ast(context)
    case ast.Not(oper) => (!predeval(oper, infs)).ast(context)
  }


  private def filter(pr: ast.Predicate, infs: Z3AST, outfs: Z3AST)
                    (implicit pathmap: Map[Path, Z3AST]): Z3AST = {
    ((predeval(pr, infs) --> idfs(infs, outfs, pathmap)) &&
     (!predeval(pr, infs) --> errfs(outfs, pathmap))).ast(context)
  }

  private def mkdir(infs: Z3AST, outfs: Z3AST, path: Path, pathmap: Map[Path, Z3AST]): Z3AST = {
    val z3parentpath = pathmap.get(path.getParent) getOrElse (throw new Exception("path not mapped"))
    val z3path = pathmap.get(path) getOrElse (throw new Exception("path not mapped"))
    val e = (pexists(z3parentpath, infs) --> (pexists(z3path, outfs) && idfs(infs, outfs, pathmap - path))) &&
            (!pexists(z3parentpath, infs) --> errfs(outfs, pathmap))
    e.ast(context)
  }

  // only for initial filesystem
  private def parentshouldexist(fs: Z3AST, parent: Z3AST, children: List[Z3AST]): Z3AST = {
    z3.mkImplies(z3.mkNot(pexists(parent,fs)),
                 z3.mkAnd((children.toSeq map {p => z3.mkNot(pexists(p, fs))}):_*))
  }

  private def idfs(infs: Z3AST, outfs: Z3AST, pathmap: Map[Path, Z3AST]): Z3AST = {
    z3.mkAnd((pathmap.toSeq map {case(_, p) => (pexists(p, infs) === pexists(p, outfs))}):_*)
  }

  private def errfs(fs: Z3AST, pathmap: Map[Path, Z3AST]): Z3AST = {
    z3.mkAnd((pathmap.toSeq map {case(_, p) => (pexists(p, fserr) === (pexists(p, fs)))}):_*)
  }

  private def eval(e: FSKATExpr,
                   initfs: Z3AST)
                   (implicit pathmap: Map[Path, Z3AST]): Z3AST /* Final FS */ = e match {

    case Id => {
      val outfs = z3.mkFreshConst("fs", fsSort)
      solver.assertCnstr(idfs(initfs, outfs, pathmap))
      outfs
    }

    case Err => {
      val outfs = z3.mkFreshConst("fs", fsSort)
      solver.assertCnstr(errfs(outfs, pathmap))
      outfs
    }

    case MkDir(p) => {
      val outfs = z3.mkFreshConst("fs", fsSort)
      solver.assertCnstr(mkdir(initfs, outfs, p, pathmap))
      outfs
    }

    case RmDir(p) => {
      val outfs = z3.mkFreshConst("fs", fsSort)
      // solver.assertCnstr(rmdir(initfs, outfs, p))
      solver.assertCnstr(mkdir(initfs, outfs, p, pathmap)) // TODO
      outfs
    }

    case Create(p) => {
      val outfs = z3.mkFreshConst("fs", fsSort)
      // solver.assertCnstr(create(initfs, outfs, p))
      solver.assertCnstr(mkdir(initfs, outfs, p, pathmap)) // TODO
      outfs
    }

    case Delete(p) => {
      val outfs = z3.mkFreshConst("fs", fsSort)
      // solver.assertCnstr(delete(initfs, outfs, p))
      solver.assertCnstr(mkdir(initfs, outfs, p, pathmap)) // TODO
      outfs
    }

    case Link(p) => {
      val outfs = z3.mkFreshConst("fs", fsSort)
      // solver.assertCnstr(link(initfs, outfs, p))
      solver.assertCnstr(mkdir(initfs, outfs, p, pathmap)) // TODO
      outfs
    }

    case Unlink(p) => {
      val outfs = z3.mkFreshConst("fs", fsSort)
      // solver.assertCnstr(unlink(initfs, outfs, p))
      solver.assertCnstr(mkdir(initfs, outfs, p, pathmap)) // TODO
      outfs
    }

    case Shell(p) => {
      val outfs = z3.mkFreshConst("fs", fsSort)
      // solver.assertCnstr(shell(initfs, outfs, p))
      solver.assertCnstr(mkdir(initfs, outfs, p, pathmap)) // TODO
      outfs
    }

    case Filter(pr) => {
      val outfs = z3.mkFreshConst("fs", fsSort)
      solver.assertCnstr(filter(pr, initfs, outfs))
      outfs
    }

    case Seqn(lhs, rhs) => eval(rhs, eval(lhs, initfs))

    case Opt(lhs, rhs) => {
      val outfs1 = eval(lhs, initfs)
      val outfs2 = eval(rhs, initfs)
      outfs2 // random TODO
    }
  }

  // The algorithm is that for every p in path 
  def toParentChildMap(p: Path): Map[Path, Set[Path]] = {

    if(p.getParent != null) {
      Map(p.getParent -> Set(p)) ++ toParentChildMap(p.getParent)
    }
    else {
      Map.empty
    }
  }

  private def mergemap(m1: Map[Path, Set[Path]],
                       m2: Map[Path, Set[Path]]): Map[Path, Set[Path]] = {

    val keys = m1.keySet ++ m2.keySet

    val tups = for (k <- keys) yield {
      val v1 = m1.get(k) getOrElse Set.empty
      val v2 = m2.get(k) getOrElse Set.empty
      (k->(v1 ++ v2))
    }

    Map((tups.toSeq):_*)
  }


  def isEquiv(e1: equiv.ast.Expr, e2: equiv.ast.Expr): Option[Boolean] = {

    solver.push

    val e1fskat = Desugar(e1)
    val e2fskat = Desugar(e2)

    val pathmap = Map((((gatherPaths(e1fskat) ++ gatherPaths(e2fskat)) map {p => (p->toZ3AST(p))}).toSeq):_*) ++ Map(Paths.get("/")->root)

    // define errfs
    solver.assertCnstr(z3.mkAnd((pathmap.toSeq.map({case(_, p) => (!pexists(p, fserr)).ast(context)})):_*))

    val fstree = (pathmap.keySet).toSeq map {p => toParentChildMap(p)} reduce(mergemap)
    solver.assertCnstr(z3.mkAnd((fstree.toSeq map {case (k, v) => parentshouldexist(initfs, pathmap(k), v.toList.map(pathmap(_)))}):_*))

    val fsfinal_e1 = eval(e1fskat, initfs)(pathmap)
    val fsfinal_e2 = eval(e2fskat, initfs)(pathmap)

    // assert that paths are distinct
    val z3paths = pathmap.values.toSeq
    solver.assertCnstr(z3.mkDistinct(z3paths: _*))

    // initfs is not the same as errfs, atleast root exists on initFS
    solver.assertCnstr(pexists(root, initfs))

    if(Some(true) != sanityCheck()) {
      printAssertions()
      solver.pop()
      println("Sanity check failed")
      return Some(false)
    }

    // Assert that final fs_s are same wrt to all the paths
    solver.assertCnstr(z3.mkNot(z3.mkAnd((pathmap.toSeq map {case(_, p) => (pexists(p, fsfinal_e1) === pexists(p, fsfinal_e2))}):_*)))

    // printAssertions()

    val result = solver.checkAssumptions() map { b => !b }

    solver.pop()

    result
  }

  val solver = z3.mkSolver

  def sanityCheck(): Option[Boolean] = {
    solver.checkAssumptions()
  }

  def printAssertions() {
    println("============================== ASSERTIONS =====================================")
    solver.getAssertions().toSeq.foreach(println)
    println("-------------------------------------------------------------------------------")
  }
}
