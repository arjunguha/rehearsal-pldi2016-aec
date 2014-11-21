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

  val root = z3.mkConst("/", pathSort)

  val pexists = z3.mkFuncDecl("pexists", Seq(pathSort, fsSort), boolSort)
  val isdir   = z3.mkFuncDecl("isdir",   Seq(pathSort, fsSort), boolSort)
  val isfile  = z3.mkFuncDecl("isfile",  Seq(pathSort, fsSort), boolSort)
  val islink  = z3.mkFuncDecl("islink",  Seq(pathSort, fsSort), boolSort)
  val iserror = z3.mkFuncDecl("iserror", Seq(fsSort), boolSort)

  private def toZ3AST(p: Path): Z3AST = z3.mkConst(p.toString, pathSort)

  private object model extends ast.OptExprModel {

    type S = Z3AST
    type B = Z3AST // The type of boolean expressions in the model
    type P = Z3AST

    var numStates = 0

    val trueB = true.ast(context)
    def falseB = false.ast(context)
    def andB(e1: B, e2: B): B = (e1 && e2).ast(context)
    def orB(e1: B, e2: B): B = (e1 || e2).ast(context)
    def notB(e: B): B = (!e).ast(context)
    def ifB(e1: B, e2: B, e3: B) = ((e1 --> e2) && (!e1 --> e3)).ast(context)
    def iffB(e1: B, e2: B) = (e1 <--> e2).ast(context)
    def impliesB(e1: B, e2: B) = (e1 --> e2).ast(context)
    def eqState(s1: S, s2: S): B = (s1 === s2)
    def mkState(): S = {
      numStates = numStates + 1
      z3.mkFreshConst("fs", fsSort)

    }

    def exists(path: P, state: S): B = pexists(path, state)
    def isDir(path: P, state: S): B = isdir(path, state)
    def isFile(path: P, state: S): B = isfile(path, state)
    def isLink(path: P, state: S): B = islink(path, state)
    def isError(s: S): B = iserror(s)
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
    isEquiv(Desugar(e1), Desugar(e2))
  }

  def isEquiv(e1fskat: FSKATExpr, e2fskat: FSKATExpr): Option[Boolean] = {

    solver.push
    model.numStates = 0

    val allpaths = ancestors(FSKATExpr.gatherPaths(e1fskat) union FSKATExpr.gatherPaths(e2fskat))

    val pathmap = HashMap(((allpaths map {p=>(p->toZ3AST(p))}).toSeq):_*) + (Paths.get("/")->root)


    // Only the root directory exists in the initial state
    for ((_, p) <- pathmap; if (p != root)) {
      solver.assertCnstr(model.notB(model.exists(p, initfs)))
    }
    solver.assertCnstr(model.exists(root, initfs))
    solver.assertCnstr(model.notB(model.isError(initfs)))

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

    def similar(s1: Z3AST, s2: Z3AST): Z3AST = {
      pathmap.values.toSeq.foldLeft(model.trueB) { (b, p) =>
        model.andB(b,  model.exists(p, s1) === model.exists(p, s2))
      }
    }

    println(s"${model.numStates} states and ${pathmap.size} paths generated in Z3")

    solver.assertCnstr((!((iserror(fsfinal_e1) && iserror(fsfinal_e2)) ||
                           similar(fsfinal_e1, fsfinal_e2))).ast(context))

                       //)

    val result = solver.checkAssumptions() map { b =>
      // if (b) {
      //   println("*************** MODEL *****************")
      //   solver.getAssertions().toSeq.foreach(println)
      //   println(solver.getModel)
      // }

      !b
    }

    solver.pop()

    result
  }

  def isSatisfiable(e: FSKATExpr): Boolean = {

    solver.push
    model.numStates = 0

    val allpaths = ancestors(FSKATExpr.gatherPaths(e))
    val pathmap = HashMap(((allpaths map {p=>(p->toZ3AST(p))}).toSeq):_*) + (Paths.get("/")->root)

    // Only the root directory exists in the initial state
    for ((_, p) <- pathmap; if (p != root)) {
      solver.assertCnstr(model.notB(model.exists(p, initfs)))
    }
    solver.assertCnstr(model.exists(root, initfs))
    solver.assertCnstr(model.notB(model.isError(initfs)))

    // assert that paths are distinct
    solver.assertCnstr(z3.mkDistinct(pathmap.values.toSeq: _*))

    // evaluate
    val fsfinal = eval(e, initfs, pathmap)
    solver.assertCnstr((!iserror(fsfinal)).ast(context))

    val result = solver.checkAssumptions()
    solver.pop()
    result getOrElse false
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
