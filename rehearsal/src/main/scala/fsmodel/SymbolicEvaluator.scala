package rehearsal.fsmodel

import java.nio.file.{Paths, Path}
import com.microsoft.z3.{ArrayExpr, Sort}
import bdd.Bdd

sealed trait Status
case object Sat extends Status
case object Unsat extends Status
case object Unknown extends Status

object Z3Helpers {

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

 def materializeArray(model: z3.Model, arr: z3.Expr, sort: z3.ArraySort)
   (implicit cxt: z3.Context, solver: z3.Solver): z3.Expr = {
   val arrFromAsArray = arr.getFuncDecl.getParameters.toList(0).getFuncDecl
   val i = model.getFuncInterp(arrFromAsArray)
   val baseAcc = cxt.mkConstArray(sort.getDomain, i.getElse)
   i.getEntries.foldLeft(baseAcc)({ case (arr, entry) =>
          cxt.mkStore(arr, entry.getArgs.head, entry.getValue)
   })
 }

  def printAssertions()(implicit solver: z3.Solver): Unit = {
    println("*** Assertions ***")
    for (assert <- solver.getAssertions) {
      println(s"$assert")
    }
  }

  def choices[A <: z3.Expr](lst: List[A])
    (implicit cxt: z3.Context, solver: z3.Solver): A = {
    val numChoices = lst.length
    assert (numChoices > 0)
    if (numChoices == 1) {
      lst.head
    }
    else {
      val x = cxt.mkFreshConst("choice", cxt.mkIntSort).asInstanceOf[z3.ArithExpr]
      solver.add(cxt.mkAnd(cxt.mkGe(x, cxt.mkInt(0)),
                           cxt.mkLt(x, cxt.mkInt(numChoices))))
      def helper(n: Int, lst: List[A]): A = lst match {
        case List(alt) => alt
        case alt :: rest => {
          cxt.mkITE(cxt.mkEq(x, cxt.mkInt(n)),
                    alt,
                    helper(n + 1, rest)).asInstanceOf[A]
        }
      }
      helper(0, lst)
    }
  }

  def freshBool(name: String)(implicit cxt: z3.Context): z3.BoolExpr = {
    cxt.mkFreshConst(name, cxt.mkBoolSort).asInstanceOf[z3.BoolExpr]
  }

  def ite[A <: z3.Expr](a: z3.BoolExpr, x: A, y: A)
    (implicit cxt: z3.Context): A = {
    cxt.mkITE(a, x, y).asInstanceOf[A]
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

  val allPaths = g.nodes.map(e => Helpers.exprPaths(e)).reduce(_ union _).toList

  object ST {

    def apply(): ST = {
      ST(cxt.mkFreshConst("b", cxt.mkBoolSort).asInstanceOf[z3.BoolExpr],
         allPaths.map(p => p -> cxt.mkFreshConst(p.toString, statSort)).toMap)
    }

    def ite(b: z3.BoolExpr, st1: ST, st2: ST): ST = {
      ST(cxt.mkITE(b, st1.isErr, st2.isErr).asInstanceOf[z3.BoolExpr],
         allPaths.map(p => p -> cxt.mkITE(b, st1.files(p), st2.files(p))).toMap)
    }
  }

  case class ST(isErr: z3.BoolExpr, files: Map[Path, z3.Expr]) {

    def isEq(other: ST): z3.BoolExpr = {
      val pathsEq = allPaths.map(p => cxt.mkEq(this.files(p), other.files(p)))
      cxt.mkAnd(cxt.mkEq(this.isErr, other.isErr),
                cxt.mkAnd(pathsEq: _*))
    }

  }

  def select(state: ST, path: Path): z3.Expr = state.files(path)

  def store(state: ST, path: Path, stat: z3.Expr): ST =
    ST(state.isErr, state.files + (path -> stat))

  type Rep = z3.Expr
  type B = z3.BoolExpr

  def trueB = cxt.mkTrue
  def falseB = cxt.mkFalse
  def notB(a: B): B = cxt.mkNot(a)
  def andB(a: B, b: B): B = cxt.mkAnd(a, b)
  def orB(a: B, b: B): B = cxt.mkOr(a, b)

  def testFileStateB(state: ST, p: Path, st: FileState): B = {
    val stat = select(state, p)
    st match {
      case IsDir => cxt.mkEq(stat, isDir)
      case DoesNotExist => cxt.mkEq(stat, doesNotExist)
      case IsFile => isIsFile(stat)
    }
  }

  def testFileHashB(state: ST, p: Path, hash: Array[Byte]): B = {
    val stat = select(state, p)
    cxt.mkAnd(isIsFile(stat),
              cxt.mkEq(cxt.mkApp(getIsFileHash, stat), hashToZ3(hash)))
  }

  def setFileHash(st: ST, p: Path, hash: Array[Byte]): ST =
    store(st, p, isFile(hash))

  def update(state: ST, p: Path, stat: FileState): ST =  {
    val stat1 = stat match {
      case IsDir =>  isDir
      case DoesNotExist =>  doesNotExist
      case IsFile =>  isFile(Array.fill(16)(0.toByte))
    }
    store(state, p, stat1)
  }

  def eqB[A <: Rep](x: A, y: A): B = cxt.mkEq(x, y)

  def evalPred(fs: ST, pred: Pred): B = pred match {
    case True => trueB
    case False => falseB
    case Not(a) => notB(evalPred(fs, a))
    case And(a, b) => andB(evalPred(fs, a), evalPred(fs, b))
    case Or(a, b) => orB(evalPred(fs, a), evalPred(fs, b))
    case TestFileState(p, st) => testFileStateB(fs, p, st)
    case TestFileHash(p, h) => testFileHashB(fs, p, h)
    case ITE(a, b, c) => ite(evalPred(fs, a),
                             evalPred(fs, b),
                             evalPred(fs, c))
  }

  def evalExpr(st: ST, expr: Expr): ST = expr match {
    case Skip => st
    case Error => ST(cxt.mkTrue, st.files)
    case Seq(p, q) => evalExpr(evalExpr(st, p), q)
    case If(a, p, q) => {
      val b = cxt.mkFreshConst("b", cxt.mkBoolSort).asInstanceOf[z3.BoolExpr]
      solver.add(cxt.mkEq(b, evalPred(st, a)))
      ST.ite(b, evalExpr(st, p), evalExpr(st, q))
    }
    case Mkdir(p) => {
      val b = cxt.mkFreshConst("b", cxt.mkBoolSort).asInstanceOf[z3.BoolExpr]
      solver.add(cxt.mkEq(b,
                          andB(testFileStateB(st, p.getParent, IsDir),
                               testFileStateB(st, p, DoesNotExist))))
      ST(cxt.mkOr(st.isErr, cxt.mkNot(b)),
         update(st, p, IsDir).files)
    }
    case CreateFile(p, h) => {
      val b = cxt.mkFreshConst("b", cxt.mkBoolSort).asInstanceOf[z3.BoolExpr]
      solver.add(cxt.mkEq(b, andB(testFileStateB(st, p.getParent, IsDir),
                                  testFileStateB(st, p, DoesNotExist))))
      ST(cxt.mkOr(st.isErr, cxt.mkNot(b)),
         setFileHash(st, p, h).files)
    }
    case Rm(p) => {
      val b = freshBool("b")
      solver.add(cxt.mkEq(b, (testFileStateB(st, p, IsFile))))
      ST(cxt.mkOr(st.isErr, cxt.mkNot(b)), update(st, p, DoesNotExist).files)
    }
    case _ => throw new IllegalArgumentException("not implemented")
  }

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
        ST.ite(b, st1, st2)
      })
    }
  }

  // def findCounterexample(interST: z3.Expr,
  //                        outST: z3.Expr,
  //                        graph: FileScriptGraph): Option[z3.Model] = {
  //   val fringe = graph.nodes.filter(_.outDegree == 0).toList
  //   if (fringe.length == 0) {
  //     pushPop {
  //       solver.add(cxt.mkNot(cxt.mkEq(outST, interST)).simplify.asInstanceOf[z3.BoolExpr])
  //       solver.check() match {
  //         case z3.Status.SATISFIABLE => Some(solver.getModel())
  //         case z3.Status.UNSATISFIABLE => None
  //         case z3.Status.UNKNOWN => throw new RuntimeException("got unknown")
  //       }
  //     }
  //   }
  //   else if (poReduction && allPairsCommute(fringe)) {
  //     val p = Block(fringe.foldRight(List[Expr]()) { (n, lst) => n :: lst }: _*)
  //     findCounterexample(evalExpr(interST, p), outST, graph -- fringe)
  //   }
  //   else {
  //     val interST1 = cxt.mkFreshConst("interST1", stateSort)
  //     solver.add(cxt.mkEq(interST1, interST).simplify.asInstanceOf[z3.BoolExpr])
  //     pushPop {
  //       fringe.toStream.map({ p =>
  //         findCounterexample(evalExpr(interST1, p), outST, graph - p)
  //       })
  //       .find(_.isDefined)
  //       .flatten
  //     }
  //   }
  // }

  def isDeterministic(): Boolean = {
    val inST = ST()
    val outST1 = evalGraph(inST, g)
    val outST2 = evalGraph(inST, g)
    solver.add(cxt.mkNot(outST1.isEq(outST2)))
    assertHashCardinality()
    solver.check() match {
      case z3.Status.SATISFIABLE => {
        false
      }
      case z3.Status.UNSATISFIABLE => true
      case z3.Status.UNKNOWN => throw new RuntimeException("got unknown")
    }

    // pushPop {
    //   val inST = cxt.mkFreshConst("inST", stateSort)
    //   val outST1 = cxt.mkFreshConst("outST", stateSort)
    //   solver.add(cxt.mkEq(outST1, evalGraphDeterministic(inST, g)))
    //   assertHashCardinality()
    //   findCounterexample(inST, outST1, g) match {
    //     case None => true
    //     case Some(model) => false
    //   }
    // }
  }

}
