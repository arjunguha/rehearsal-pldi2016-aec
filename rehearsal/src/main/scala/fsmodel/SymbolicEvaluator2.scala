package exp

import rehearsal._
import fsmodel.FileScriptGraph
import smtlib._
import parser._
import Commands._
import Terms._
import theories.Core._
//import theories.FixedSizeBitVectors._
import interpreters.Z3Interpreter
import CommandsResponses._
import java.nio.file.{Path, Paths}
import rehearsal.fsmodel.{Block, Expr}

object SymbolicEvaluator2 {
  def exprEquals(e1: fsmodel.Expr, e2: fsmodel.Expr): Boolean = {
    new SymbolicEvaluatorImpl((e1.paths union e2.paths).toList).exprEquals(e1, e2)
  }
  def predEquals(a: fsmodel.Pred, b: fsmodel.Pred): Boolean = {
    new SymbolicEvaluatorImpl((a.readSet union b.readSet).toList).predEquals(a, b)
  }
  def isDeterministic(g: FileScriptGraph): Boolean = {
    new SymbolicEvaluatorImpl(g.nodes.map(e => e.paths).reduce(_ union _).toList).isDeterministic(g)
  }
}
class SymbolicEvaluatorImpl(allPaths: List[Path]) {
  import scala.language.implicitConversions

  implicit def stringToQualID(str: String): QualifiedIdentifier = {
    QualifiedIdentifier(Identifier(SSymbol(str)))
  }

  var nextName = 0
  def freshName(base: String = "x"): SSymbol = {
    nextName = nextName + 1
    SSymbol(s"$base$nextName")
  }

  val interpreter : Interpreter = Z3Interpreter.buildDefault

  def process(command: Command) : CommandResponse = {
    print(command)
    val resp = interpreter.eval(command)
    println(s"; $resp")
    resp
  }

    process(DeclareSort(SSymbol("hash"), 0))

    val hashSort = Sort(SimpleIdentifier(SSymbol("hash")))

    val hash0 = SSymbol("hash0")
    process(DeclareConst(hash0, hashSort))

    // type stat = IsDir | DoesNotExist | IsFile of hash
    process(DeclareDatatypes(Seq((SSymbol("stat"),
      Seq(Constructor(SSymbol("IsDir"), Seq()),
        Constructor(SSymbol("DoesNotExist"), Seq()),
        Constructor(SSymbol("IsFile"), Seq((SSymbol("hash"), hashSort))))))))

    val statSort = Sort(SimpleIdentifier(SSymbol("stat")))

    case class ST(isErr: Term, paths: Map[Path, Term])

    def freshST(): ST = {
      val paths = allPaths.map(p => {
        val z = freshName("path")
        process(DeclareConst(z, statSort))
        (p, QualifiedIdentifier(Identifier(z)))
      })
      val isErr = freshName("isErr")
      process(DeclareConst(isErr, BoolSort()))
      ST(QualifiedIdentifier(Identifier(isErr)), paths.toMap)
    }

    def stEquals(st1: ST, st2: ST): Term = {
      And(Equals(st1.isErr, st2.isErr),
        And(allPaths.map(p => Equals(st1.paths(p), st2.paths(p))): _*))
    }

    def evalPred(st: ST, pred: fsmodel.Pred): Term = pred match {
      case fsmodel.True => True()
      case fsmodel.False => False()
      case fsmodel.Not(a) => Not(evalPred(st, a))
      case fsmodel.And(a, b) => And(evalPred(st, a), evalPred(st, b))
      case fsmodel.Or(a, b) => Or(evalPred(st, a), evalPred(st, b))
      case fsmodel.TestFileState(p, fsmodel.IsDir) => Equals(st.paths(p), QualifiedIdentifier(Identifier(SSymbol("IsDir"))))
      case fsmodel.TestFileState(p, fsmodel.DoesNotExist) => Equals(st.paths(p), QualifiedIdentifier(Identifier(SSymbol("DoesNotExist"))))
      case fsmodel.TestFileState(p, fsmodel.IsFile) =>
        FunctionApplication(QualifiedIdentifier(Identifier(SSymbol("is-IsFile"))), Seq(st.paths(p)))
      //    case fsmodel.TestFileHash(p, h) => {
      //      val stat = st.select(p)
      //      isIsFile(stat) && (cxt.mkApp(getIsFileHash, stat) === hashToZ3(h))
      //    }
      //    case fsmodel.ITE(a, b, c) => ite(evalPred(st, a),
      //      evalPred(st, b),
      //      evalPred(st, c))
      case _ => throw NotImplemented(pred.toString)
    }

    def predEquals(a: fsmodel.Pred, b: fsmodel.Pred): Boolean = {
      try {
        process(Push(1))
        val st = freshST()
        process(Assert(Not(Equals(evalPred(st, a), evalPred(st, b)))))
        process(CheckSat()) match {
          case CheckSatStatus(SatStatus) => {
            process(GetModel())
            false
          }
          case CheckSatStatus(UnsatStatus) => true
          case CheckSatStatus(UnknownStatus) => throw Unexpected("got unknown")
          case s => throw Unexpected(s"got $s from check-sat")
        }
      }
      finally {
        process(Pop(1))
      }
    }

    def evalExpr(st: ST, expr: fsmodel.Expr): ST = expr match {
      case fsmodel.Skip => st
      case fsmodel.Error => ST(True(), st.paths)
      case fsmodel.Seq(p, q) => evalExpr(evalExpr(st, p), q)
      case fsmodel.If(a, e1, e2) => {
        val st1 = evalExpr(st, e1)
        val st2 = evalExpr(st, e2)
        val b = evalPred(st, a)
        ST(ITE(b, st1.isErr, st2.isErr),
          allPaths.map(p => (p, ITE(b, st1.paths(p), st2.paths(p)))).toMap)
      }
      case fsmodel.CreateFile(p, h) => {
        val pre = And(Equals(st.paths(p), QualifiedIdentifier(Identifier(SSymbol("DoesNotExist")))),
          Equals(st.paths(p.getParent), QualifiedIdentifier(Identifier(SSymbol("IsDir")))))
        ST(Or(st.isErr, Not(pre)),
          st.paths + (p -> FunctionApplication("IsFile", Seq("hash0"))))
      }
      case fsmodel.Mkdir(p) => {
        val pre = And(Equals(st.paths(p), "DoesNotExist"),
          Equals(st.paths(p.getParent), "IsDir"))
        ST(Or(st.isErr, Not(pre)),
          st.paths + (p -> "IsDir"))
      }
      case fsmodel.Rm(p) => {
        val pre = And(Equals(st.paths(p), FunctionApplication("IsFile", Seq("hash0"))))
        ST(Or(st.isErr, Not(pre)),
          st.paths + (p -> "DoesNotExist"))
      }
      case fsmodel.Cp(src, dst) => {
        val pre = And(Equals(st.paths(src), FunctionApplication("IsFile", Seq("hash0"))),
          Equals(st.paths(dst.getParent), "IsDir"),
          Equals(st.paths(dst), "DoesNotExist"))
        ST(Or(st.isErr, Not(pre)),
          st.paths + (dst -> FunctionApplication("IsFile", Seq("hash0"))))
      }
    }

    def exprEquals(e1: fsmodel.Expr, e2: fsmodel.Expr): Boolean = {
      try {
        process(Push(1))
        val st = freshST()
        val st1 = evalExpr(st, e1)
        val st2 = evalExpr(st, e2)

        process(Assert(Not(stEquals(st1, st2))))
        process(CheckSat()) match {
          case CheckSatStatus(SatStatus) => {
            process(GetModel())
            false
          }
          case CheckSatStatus(UnsatStatus) => true
          case CheckSatStatus(UnknownStatus) => throw Unexpected("got unknown")
          case s => throw Unexpected(s"got $s from check-sat")
        }
      }
      finally {
        process(Pop(1))
      }
    }

    def allPairsCommute(lst: List[FileScriptGraph#NodeT]): Boolean = {
      lst.combinations(2).forall {
        case List(a,b) => a.value.commutesWith(b.value)
      }
    }

    def evalGraph(st: ST, g: FileScriptGraph): ST = {
      val fringe = g.nodes.filter(_.outDegree == 0).toList
      if (fringe.length == 0) {
        st
      }
      else if (allPairsCommute(fringe)) {
        // Create a sequence of the programs in fringe. The ridiculous foldRight,
        // which is just the identity function, is a hack to coerce the
        // inner nodes to outer nodes in ScalaGraph.
        val p = Block(fringe.foldRight(List[Expr]()) { (n, lst) => n :: lst }: _*)
        evalGraph(evalExpr(st, p), g -- fringe)
      }
      else {
        fringe.map(p => evalGraph(evalExpr(st, p), g - p)).reduce({ (st1: ST, st2: ST) =>
          val b = process(DeclareConst(freshName("choice"), BoolSort()))
          ST(ITE("choice", st1.isErr, st2.isErr),
            allPaths.map(p => p -> ITE("choice", st1.paths(p),st2.paths(p))).toMap)
        })
      }
    }

    def isDeterministic(g: FileScriptGraph): Boolean = {
      val inST = freshST()
      val outST1 = evalGraph(inST, g)
      val outST2 = evalGraph(inST, g)
      process(Assert(stEquals(outST1, outST2)))
     // assertHashCardinality()
      process(CheckSat()) match {
        case CheckSatStatus(SatStatus) => {
          process(GetModel())
          false
        }
        case CheckSatStatus(UnsatStatus) => true
        case CheckSatStatus(UnknownStatus) => throw new RuntimeException("got unknown")
        case s => throw Unexpected(s"got $s from check-sat")
      }

    }

  /*
    val interpreter : Interpreter = Z3Interpreter.buildDefault

    def process(command: Command) : CommandResponse = {
      print(command)
      interpreter.eval(command)
    }

    process(DeclareConst(SSymbol("x"), BitVectorSort(5)))
    process(DeclareConst(SSymbol("y"), BitVectorSort(5)))
    process(Assert(Equals(QualifiedIdentifier(Identifier(SSymbol("x")), None),
      QualifiedIdentifier(Identifier(SSymbol("y")), None))))
    process(CheckSat())
    val model = process(GetModel()) match {
      case GetModelResponseSuccess(model) => model
      case other => throw new RuntimeException(s"GetModel() expected model response but received $other")
    }
    println(model)
    for (sexpr <- model) {
      sexpr match {
        case SList(sexprs) => println(sexprs)
        case DefineFun(FunDef(name, _, _, body)) => println(s"$name = $body")
        case _ => throw new RuntimeException("eye em le ded...")
      }
    }
  */

}