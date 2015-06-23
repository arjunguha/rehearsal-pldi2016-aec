package rehearsal.fsmodel

import rehearsal._
import java.nio.file.{Paths, Path}
import com.microsoft.z3.{ArrayExpr, Sort}
import bdd.Bdd

sealed trait Status
case object Sat extends Status
case object Unsat extends Status
case object Unknown extends Status

object Z3Helpers {

  import scala.language.implicitConversions
  import com.microsoft.z3

  def pushPop[A](body: => A)(implicit solver: z3.Solver): A = {
    try {
      solver.push()
      body
    }
    finally {
      solver.pop()
    }
  }

  def printAssertions()(implicit solver: z3.Solver): Unit = {
    println("*** Assertions ***")
    for (assert <- solver.getAssertions) {
      println(s"$assert")
    }
  }

  def freshBool(name: String)(implicit cxt: z3.Context): z3.BoolExpr = {
    cxt.mkFreshConst(name, cxt.mkBoolSort).asInstanceOf[z3.BoolExpr]
  }

  def ite[A <: z3.Expr](a: z3.BoolExpr, x: A, y: A)
    (implicit cxt: z3.Context): A = {
    cxt.mkITE(a, x, y).asInstanceOf[A]
  }

  implicit class RichExpr(e1: z3.Expr) {

    def ===(e2: z3.Expr)(implicit cxt: z3.Context): z3.BoolExpr = {
      cxt.mkEq(e1, e2)
    }
  }

  implicit class RichBoolExpr(e1: z3.BoolExpr) {

    def &&(e2: z3.BoolExpr)(implicit cxt: z3.Context): z3.BoolExpr = {
      cxt.mkAnd(e1, e2)
    }

    def ||(e2: z3.BoolExpr)(implicit cxt: z3.Context): z3.BoolExpr = {
      cxt.mkOr(e1, e2)
    }

    def unary_!()(implicit cxt: z3.Context): z3.BoolExpr = cxt.mkNot(e1)

  }

  implicit def boolToZ3(b: Boolean)(implicit cxt: z3.Context): z3.BoolExpr = {
    cxt.mkBool(b)
  }

}

object SymbolicEvaluator {

  def isDeterministic(g: FileScriptGraph, poReduction: Boolean = true): Boolean = {
    new SymbolicEvaluatorImpl(poReduction, g).isDeterministic()
  }

}

class SymbolicEvaluatorImpl(poReduction: Boolean, g: FileScriptGraph)  {

  import com.microsoft.z3
  import Z3Helpers._

  implicit val cxt = new z3.Context()
  implicit val solver = cxt.mkSolver()

  // We treat each hashcode as an uninterpreted value of sort 'hashSort'.
  // 'fileHashMap' maps each hash to a unique constant. 'hashToZ3' looks up
  // the constant for a hashcode in 'fileHashMap' and creates it if it doesn't
  // exist. 'assertHashCardinality' asserts that all hashes are unique and no
  // other hashes exist.
  //
  // One wart: hashes are Array[Byte], and arrays don't have proper hash
  // functions in Java. We convert to List[Byte], which does the right thing.
  val hashSort = cxt.mkUninterpretedSort("Hash")

  val fileHashMap = scala.collection.mutable.Map[List[Byte], z3.Expr]()

  def hashToZ3(hash: Array[Byte]): z3.Expr = fileHashMap.get(hash.toList) match {
    case Some(z) => z
    case None => {
      val z = cxt.mkFreshConst("hash", hashSort)
      fileHashMap += (hash.toList -> z)
      z
    }
  }

  // Don't allow hashToZ3 to create more hashes after this has been evaluated.
  def assertHashCardinality(): Unit = {
    val hashes = fileHashMap.values.toList
    if (hashes.isEmpty) {
      return
    }
    solver.add(cxt.mkDistinct(hashes: _*))
    val s = cxt.mkSymbol("p")
    val p1 = cxt.mkConst(s, hashSort)

    solver.add(cxt.mkForall(Array(hashSort), Array(s),
               cxt.mkOr(hashes.map(p2 => cxt.mkEq(p1, p2)): _*),
               1, null, null, cxt.mkSymbol("q"), cxt.mkSymbol("sk")))
  }


  // This is essentially the following:
  //
  // type stat = IsDir | DoesNotExist | IsFile of hash
  val isDirCtor = cxt.mkConstructor("IsDir", "isIsDir", null, null, null)
  val doesNotExistCtor = cxt.mkConstructor("DoesNotExist", "isDoesNotExist",
    null, null, null)
  val isFileCtor = cxt.mkConstructor("IsFile", "isIsFile",
    Array[String]("IsFile-hash"), Array[Sort](hashSort), Array(0))
  val statSort = cxt.mkDatatypeSort("Stat",
    Array(isDirCtor, doesNotExistCtor, isFileCtor))

  val Array(getIsFileHash) = isFileCtor.getAccessorDecls

  def isFile(hash: Array[Byte]) = cxt.mkApp(isFileCtor.ConstructorDecl, hashToZ3(hash))
  def isDir = cxt.mkConst(isDirCtor.ConstructorDecl)
  def doesNotExist = cxt.mkConst(doesNotExistCtor.ConstructorDecl())
  def isIsFile(e: z3.Expr): z3.BoolExpr = {
    cxt.mkApp(isFileCtor.getTesterDecl(), e).asInstanceOf[z3.BoolExpr]
  }


  // A state ("ST") is a collection of expressions that define program state.
  // 'isErr' is true if the state is erroneous. 'paths' is a map from every
  // path (from a finite universe of paths) to a 'statSort' that determines the
  // state of the path. Path-states are meaningless if 'isErr' is true.

  val allPaths = g.nodes.map(e => Helpers.exprPaths(e)).reduce(_ union _).toList

  case class ST(isErr: z3.BoolExpr, paths: Map[Path, z3.Expr]) {

    // Two states are equal if both are in error or both are not in error and
    // all their paths are in the same state. We could work with a stricter
    // notion of equality too (i.e., all components are the same).
    def ===(other: ST): z3.BoolExpr = {
      val pathsEq = allPaths.map(p => cxt.mkEq(this.paths(p), other.paths(p)))
      (this.isErr && other.isErr)  ||
      (!this.isErr && !other.isErr && cxt.mkAnd(pathsEq: _*))
    }

   def select(path: Path): z3.Expr = paths(path)

   def store(path: Path, stat: z3.Expr): ST = ST(isErr, paths + (path -> stat))

   def setErr(b: z3.BoolExpr): ST = ST(b, paths)

  }

  object ST {

    // Creates a fresh state where the isErr bit and every path are bound
    // to fresh variables.
    def apply(): ST = {
      ST(freshBool("isErr"),
         allPaths.map(p => p -> cxt.mkFreshConst(p.toString, statSort)).toMap)
    }

    // Branching is messy. Suppose we want to write this expression in Z3, where
    // b is a Z3 boolean:
    //
    // if (b) ST(err1, { p11, p12, ...}) else ST(err2, { p21, p22, ... })
    //
    // Since ST is not a Z3 value, we can't directly turn it into a Z3
    // conditional. instead, we need to "push the b inwards":
    //
    // ST(b ? err1 : err2, { b ? p11 : p21, b ? p21 : p22, ... })
    def test(b: z3.BoolExpr, st1: ST, st2: ST): ST = {
      ST(ite(b, st1.isErr, st2.isErr),
         allPaths.map(p => p -> ite(b, st1.paths(p), st2.paths(p))).toMap)
    }

  }

  def evalPred(st: ST, pred: Pred): z3.BoolExpr = pred match {
    case True => true
    case False => false
    case Not(a) => !evalPred(st, a)
    case And(a, b) => evalPred(st, a) && evalPred(st, b)
    case Or(a, b) => evalPred(st, a) || evalPred(st, b)
    case TestFileState(p, IsDir) => st.select(p) === isDir
    case TestFileState(p, DoesNotExist) => st.select(p) === doesNotExist
    case TestFileState(p, IsFile) => isIsFile(st.select(p))
    case ITE(a, b, c) => ite(evalPred(st, a),
                             evalPred(st, b),
                             evalPred(st, c))
  }

  def evalExpr(st: ST, expr: Expr): ST = expr match {
    case Skip => st
    case Error => ST(true, st.paths)
    case Seq(p, q) => evalExpr(evalExpr(st, p), q)
    case If(a, p, q) => {
      val b = freshBool("if")
      solver.add(b === evalPred(st, a))
      ST.test(b, evalExpr(st, p), evalExpr(st, q))
    }
    case Mkdir(p) => {
      val b = freshBool("b")
      solver.add(b === (st.select(p.getParent) === isDir &&
                        st.select(p) === doesNotExist))
      st.store(p, isDir).setErr(st.isErr || !b)
    }
    case CreateFile(p, h) => {
      val b = freshBool("b")
      solver.add(b === (st.select(p.getParent) === isDir &&
                        st.select(p) === doesNotExist))
      st.store(p, isFile(h)).setErr(st.isErr || !b)
    }
    case Rm(p) => {
      val b = freshBool("b")
      solver.add(b === isIsFile(st.select(p)))
      st.store(p, doesNotExist).setErr(st.isErr || !b)
    }
    case _ => throw NotImplemented(expr.toString)
  }

  def allPairsCommute(lst: List[FileScriptGraph#NodeT]): Boolean = {
    lst.combinations(2).forall {
      case List(a,b) => a.value.commutesWith(b.value)
    }
  }

 // Needs to be a relation to encode non-determinism
  def evalGraph(st: ST, g: FileScriptGraph): ST = {
    val fringe = g.nodes.filter(_.outDegree == 0).toList
    if (fringe.length == 0) {
      st
    }
    else if (poReduction && allPairsCommute(fringe)) {
      // Create a sequence of the programs in fringe. The ridiculous foldRight,
      // which is just the identity function, is a hack to coerce the
      // inner nodes to outer nodes in ScalaGraph.
      val p = Block(fringe.foldRight(List[Expr]()) { (n, lst) => n :: lst }: _*)
      evalGraph(evalExpr(st, p), g -- fringe)
    }
    else {
      fringe.map(p => evalGraph(evalExpr(st, p), g - p)).reduce({ (st1, st2) =>
        val b = cxt.mkFreshConst("choice", cxt.mkBoolSort).asInstanceOf[z3.BoolExpr]
        ST.test(b, st1, st2)
      })
    }
  }

  def isDeterministic(): Boolean = {
    val inST = ST()
    val outST1 = evalGraph(inST, g)
    val outST2 = evalGraph(inST, g)
    solver.add(cxt.mkNot(outST1 === outST2))
    assertHashCardinality()
    solver.check() match {
      case z3.Status.SATISFIABLE => {
        false
      }
      case z3.Status.UNSATISFIABLE => true
      case z3.Status.UNKNOWN => throw new RuntimeException("got unknown")
    }

  }

}
