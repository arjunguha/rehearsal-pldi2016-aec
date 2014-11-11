package equiv.sat

import equiv._
import equiv.desugar._
import equiv.ast

import z3.scala._
import z3.scala.dsl._
import z3.scala.dsl.Operands._

import java.nio.file.{Paths, Path}

import scala.collection.immutable.HashMap
import scala.annotation.tailrec

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

  private def toZ3AST(p: Path): Z3AST = z3.mkConst(p.toString, pathSort)

  private object model extends ast.ExprModel {

    type S = Z3AST
    type B = Z3AST // The type of boolean expressions in the model
    type P = Z3AST

    val trueB = true.ast(context)
    def falseB = false.ast(context)
    def andB(e1: B, e2: B): B = (e1 && e2).ast(context)
    def orB(e1: B, e2: B): B = (e1 || e2).ast(context)
    def notB(e: B): B = (!e).ast(context)
    def ifB(e1: B, e2: B, e3: B) = ((e1 --> e2) && (!e1 --> e3)).ast(context)
    def iffB(e1: B, e2: B) = (e1 <--> e2).ast(context)
    def eqState(s1: S, s2: S): B = (s1 === s2)
    def errState: S = fserr
    def mkState(): S = z3.mkFreshConst("fs", fsSort)

    def exists(path: P, state: S): B = pexists(path, state)
    def isDir(path: P, state: S): B = isdir(path, state)
    def isFile(path: P, state: S): B = isfile(path, state)
    def isLink(path: P, state: S): B = islink(path, state)

  }

  private def eval(e: FSKATExpr, initfs: Z3AST, pathmap: Map[Path, Z3AST]): Z3AST  = {
    val (b, s) = model.eval(e, pathmap, initfs)
    solver.assertCnstr(b)
    s
  }

  private def parentshouldexist(fs: Z3AST, pathmap: Map[Path, Z3AST]): Z3AST = {

    import collection.mutable.{HashMap => mutHashMap}
    import collection.mutable.{Set => mutSet}

    // Convert to parent child map
    val flat_fstree = mutHashMap.empty[Path, mutSet[Path]]
    pathmap.keySet.foreach ((p) => {
        val parent = p.getParent
        if (null != parent) {
          val s = flat_fstree.get(parent) getOrElse mutSet.empty
          flat_fstree.put(parent, (s + p))
        }
      })

    z3.mkAnd((flat_fstree.map({ case (p, ch) => {
      z3.mkImplies(z3.mkNot(pexists(pathmap(p),fs)),
                   z3.mkAnd((ch.toSeq map {p => z3.mkNot(pexists(pathmap(p), fs))}):_*))
    }}).toSeq):_*)
  }

  def isEquiv(e1: equiv.ast.Expr, e2: equiv.ast.Expr): Option[Boolean] = {

    solver.push

    val e1fskat = Desugar(e1)
    val e2fskat = Desugar(e2)

    val allpaths = ancestors(FSKATExpr.gatherPaths(e1fskat) union FSKATExpr.gatherPaths(e2fskat))

    val pathmap = HashMap(((allpaths map {p=>(p->toZ3AST(p))}).toSeq):_*) + (Paths.get("/")->root)

    // define errfs
    solver.assertCnstr(z3.mkAnd((pathmap.toSeq.map({case(_, p) => (!pexists(p, fserr)).ast(context)})):_*))

    // assert this condition for only initial FS and all FS derived from initial FS will follow
    solver.assertCnstr(parentshouldexist(initfs, pathmap))

    val fsfinal_e1 = eval(e1fskat, initfs, pathmap)
    val fsfinal_e2 = eval(e2fskat, initfs, pathmap)

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
