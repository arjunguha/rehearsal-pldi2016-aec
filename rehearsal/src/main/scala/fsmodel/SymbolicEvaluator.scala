package rehearsal.fsmodel

import java.nio.file.{Paths, Path}
import com.microsoft.z3.{ArrayExpr, Sort}
import bdd.Bdd

sealed trait Status
case object Sat extends Status
case object Unsat extends Status
case object Unknown extends Status

trait SymbolicEvaluator {

  val poReduction: Boolean

  type Rep
  type FS <: Rep
  type B <: Rep
  type ST <: Rep

  def trueB: B
  def falseB: B
  def notB(a: B): B
  def andB(a: B, b: B): B
  def orB(a: B, b: B): B
  def ite[A <: Rep](a: B, x: A, y: A): A
  def testFileStateB(fs: FS, p: Path, st: FileState): B

  def ok(fs: FS): ST
  def error: ST
  def matchST[A <: Rep](st : ST, err: A)(ok: FS => A): A
  def update(fs: FS, p: Path, st: FileState): FS

  def choices[A <: Rep](lst: List[A]): A
  def fresh[A <: Rep](x: ST => A): A
  def eqB[A <: Rep](x: A, y: A): B

  def check(b: B): Status

  def evalPred(fs: FS, pred: Pred): B = pred match {
    case True => trueB
    case False => falseB
    case Not(a) => notB(evalPred(fs, a))
    case And(a, b) => andB(evalPred(fs, a), evalPred(fs, b))
    case Or(a, b) => orB(evalPred(fs, a), evalPred(fs, b))
    case TestFileState(p, st) => testFileStateB(fs, p, st)
    case ITE(a, b, c) => ite(evalPred(fs, a),
                             evalPred(fs, b),
                             evalPred(fs, c))
  }

  def evalExpr(st: ST, expr: Expr): ST = expr match {
    case Skip => st
    case Error => error
    case Seq(p, q) => matchST(st, error) { fs => evalExpr(ok(fs), q) }
    case If(a, p, q) => matchST(st, error) { fs =>
      ite(evalPred(fs, a), evalExpr(st, p), evalExpr(st, q))
    }
    case Cp(_, _) => throw new IllegalArgumentException("not implemented")
    case Mkdir(p) => matchST(st, error) { fs =>
      ite(andB(testFileStateB(fs, p.getParent, IsDir),
               testFileStateB(fs, p, DoesNotExist)),
          ok(update(fs, p, IsDir)),
          error)
    }
    case CreateFile(p, _) => matchST(st, error) { fs =>
      ite(andB(testFileStateB(fs, p.getParent, IsDir),
               testFileStateB(fs, p, DoesNotExist)),
          ok(update(fs, p, IsFile)),
          error)
    }
    case Rm(p) => matchST(st, error) { fs =>
      ite(testFileStateB(fs, p, IsFile),
          ok(update(fs, p, DoesNotExist)),
          error)
    }
  }

  // Needs to be a relation to encode non-determinism
  def evalGraph(st: ST, g: FileScriptGraph): ST = matchST(st, error) { fs =>
    val fringe = g.nodes.filter(_.outDegree == 0).toList
    if (fringe.length == 0) {
      st
    }
    else if (poReduction && fringe.combinations(2).forall {
                              case List(a, b) => a.commutesWith(b)
                            }) {
      // Create a sequence of the programs in fringe. The ridiculous foldRight,
      // which is just the identity function, is a hack to coerce the
      // inner nodes to outer nodes in ScalaGraph.
      val p = Block(fringe.foldRight(List[Expr]()) { (n, lst) => n :: lst }: _*)
      evalGraph(evalExpr(st, p), g -- fringe)
    }
    else {
      choices(fringe.map(p => evalGraph(evalExpr(st, p), g - p)))
    }
  }

}

object SymbolicEvaluator {

  def apply(poReduction: Boolean): SymbolicEvaluator = {
    new SymbolicEvaluatorImpl(poReduction)
  }

  def isDeterministic(g: FileScriptGraph, poReduction: Boolean = true): Boolean = {
    val eval = SymbolicEvaluator(poReduction)
    import eval._
    val formula = fresh { inST =>
      notB(eqB(evalGraph(inST, g), evalGraph(inST, g)))
    }
    check(formula) == Unsat
  }

}

class SymbolicEvaluatorImpl(val poReduction: Boolean) extends SymbolicEvaluator {

  import com.microsoft.z3

  val cxt = new z3.Context()
  val solver = cxt.mkSolver()

  val pathSort = cxt.mkUninterpretedSort("Path")

  val statSort  = cxt.mkEnumSort("Stat", "IsDir", "IsFile", "DoesNotExist")
  val Array(isDir, isFile, doesNotExist) = statSort.getConsts()
  val fileStateMap = Map[FileState, z3.Expr](IsDir -> isDir, IsFile -> isFile,
                         DoesNotExist -> doesNotExist)


  val fsSort = cxt.mkArraySort(pathSort, statSort)

  val pathMap = scala.collection.mutable.Map[Path, z3.Expr]()

  def pathToZ3(p: Path): z3.Expr = pathMap.get(p) match {
    case Some(z) => z
    case None => {
      val z = cxt.mkConst(p.toString, pathSort)
      pathMap += (p -> z)
      z
    }
  }


  type Rep = z3.Expr
  type B = z3.BoolExpr
  type FS = z3.ArrayExpr
  type ST = z3.Expr

  def trueB = cxt.mkTrue
  def falseB = cxt.mkFalse
  def notB(a: B): B = cxt.mkNot(a)
  def andB(a: B, b: B): B = cxt.mkAnd(a, b)
  def orB(a: B, b: B): B = cxt.mkOr(a, b)
  def ite[A <: Rep](a: B, x: A, y: A): A = {
    cxt.mkITE(a, x, y).asInstanceOf[A]
  }
  def testFileStateB(fs: FS, p: Path, st: FileState): B = {
    cxt.mkEq(cxt.mkSelect(fs, pathToZ3(p)), fileStateMap(st))
  }


  val errorCtor = cxt.mkConstructor("error", "is_error", null, null, null)
  val okCtor = cxt.mkConstructor("ok", "is_ok", Array[String]("ok_state"),
                                  Array[Sort](fsSort), Array(0))
  val stateSort = cxt.mkDatatypeSort("State", Array(errorCtor, okCtor))
  val Array(getOkFS) = okCtor.getAccessorDecls


  def ok(fs: FS) = cxt.mkApp(okCtor.ConstructorDecl, fs)

  def error: ST = cxt.mkConst(errorCtor.ConstructorDecl())

  def matchST[A <: Rep](st : ST, err: A)(ok: FS => A): A = {
    cxt.mkITE(cxt.mkEq(st, error),
              err,
              ok(cxt.mkApp(getOkFS, st).asInstanceOf[FS])).asInstanceOf[A]
  }

  def update(fs: FS, p: Path, st: FileState): FS = {
    cxt.mkStore(fs, pathToZ3(p), fileStateMap(st))
  }

  def choices[A <: Rep](lst: List[A]): A = {
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

  def fresh[A <: Rep](f: ST => A): A = {
    val x = cxt.mkFreshConst("st", stateSort)
    f(x)
  }

  def eqB[A <: Rep](x: A, y: A): B = cxt.mkEq(x, y)

  def assertPathCardinality(): Unit = {
    val paths = pathMap.values.toList
    if (paths.isEmpty) {
      return
    }
    solver.add(cxt.mkDistinct(paths: _*))
    val s = cxt.mkSymbol("p")
    val p1 = cxt.mkConst(s, pathSort)

    solver.add(cxt.mkForall(Array(pathSort), Array(s),
               cxt.mkOr(paths.map(p2 => cxt.mkEq(p1, p2)): _*),
               1, null, null, cxt.mkSymbol("q"), cxt.mkSymbol("sk")))
  }

  def check(b: B): Status = {
    solver.push()
    assertPathCardinality()
    solver.push()
    assert(solver.check() == z3.Status.SATISFIABLE)
    solver.pop()
    solver.add(b)
    val r = solver.check()
    solver.pop()
    r match {
      case z3.Status.SATISFIABLE => Sat
      case z3.Status.UNSATISFIABLE => Unsat
      case z3.Status.UNKNOWN => Unknown
      case _ => throw new RuntimeException("unexpected status from Z3")
    }

  }


}
