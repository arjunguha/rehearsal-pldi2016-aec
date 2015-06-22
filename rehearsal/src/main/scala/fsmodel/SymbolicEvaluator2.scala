package exp

import rehearsal.fsmodel.Eval._

case class SMTError(resp: smtlib.parser.CommandsResponses.FailureResponse)
  extends RuntimeException(resp.toString)

class SMT(outputFile: Option[String]) extends com.typesafe.scalalogging.LazyLogging {

  import java.nio.file._
  import smtlib.parser.Commands._
  import smtlib.parser.CommandsResponses._
  import smtlib.interpreters.Z3Interpreter

  private val interpreter = Z3Interpreter.buildDefault

  private val outputPath = outputFile.map(p => Paths.get(p))

  def process(command: Command) : CommandResponse = {
    logger.debug(command.toString)

    outputPath match {
      case None => ()
      case Some(p) => {
        Files.write(p, command.toString.getBytes, StandardOpenOption.APPEND,
                    StandardOpenOption.CREATE)
        Files.write(p, "\n".getBytes, StandardOpenOption.APPEND)
      }
    }

    val resp = interpreter.eval(command)
    resp match {
      case Error(msg) => {
        logger.error(s"Error from SMT solver: $msg")
        throw SMTError(Error(msg))
      }
      case Unsupported => {
        logger.error("Unsupported from SMT solver")
        throw SMTError(Unsupported)
      }
      case _ => {
        logger.debug(resp.toString)
        resp
      }
    }
  }

}

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
import rehearsal.fsmodel.{Block, Expr, HashHelper}

object SymbolicEvaluator2 {
  def exprEquals(e1: fsmodel.Expr, e2: fsmodel.Expr): Boolean = {
    new SymbolicEvaluatorImpl((e1.paths union e2.paths).toList,
                    HashHelper.exprHashes(e1) union HashHelper.exprHashes(e2), None).exprEquals(e1, e2)
  }
  def exprEqualsPrime(e1: fsmodel.Expr, e2: fsmodel.Expr): Option[Option[State]] = {
    new SymbolicEvaluatorImpl((e1.paths union e2.paths).toList,
                    HashHelper.exprHashes(e1) union HashHelper.exprHashes(e2), None).exprEqualsPrime(e1, e2)
  }
  def predEquals(a: fsmodel.Pred, b: fsmodel.Pred): Boolean = {
    new SymbolicEvaluatorImpl((a.readSet union b.readSet).toList, Set(), None).predEquals(a, b)
  }
  def isDeterministic(g: FileScriptGraph,
                      logFile: Option[String] = None): Boolean = {
    new SymbolicEvaluatorImpl(
      g.nodes.map(e => e.paths).reduce(_ union _).toList,
      g.nodes.map(e => HashHelper.exprHashes(e)).reduce(_ union _),
      logFile
      ).isDeterministic(g)
  }
}

class SymbolicEvaluatorImpl(allPaths: List[Path],
                            hashes: Set[List[Byte]],
                            logFile: Option[String]) {
  import scala.language.implicitConversions

  implicit def stringToQualID(str: String): QualifiedIdentifier = {
    QualifiedIdentifier(Identifier(SSymbol(str)))
  }

  implicit def symbolToQualID(s: SSymbol): QualifiedIdentifier = {
    QualifiedIdentifier(Identifier(s))
  }

  var nextName = 0
  def freshName(base: String = "x"): SSymbol = {
    nextName = nextName + 1
    SSymbol(s"$base$nextName")
  }

  val smt = new SMT(logFile)
  import smt.process

    process(DeclareSort(SSymbol("hash"), 0))

    val hashSort = Sort(SimpleIdentifier(SSymbol("hash")))

    def hashToTerm(l: List[Byte]): (List[Byte], Term) ={
      val x = freshName("hash")
      process(DeclareConst(x, hashSort))
      (l, QualifiedIdentifier(Identifier(x)))
    }

    val hashToZ3: Map[List[Byte], Term] = hashes.toList.map(hashToTerm).toMap
    if(hashToZ3.size != 0)  process(Assert(FunctionApplication("distinct", hashToZ3.values.toSeq)))

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
      Or(And(st1.isErr, st2.isErr),
         And(Not(st1.isErr), Not(st2.isErr),
             And(allPaths.map(p => Equals(st1.paths(p), st2.paths(p))): _*)))
    }

    def evalPred(st: ST, pred: fsmodel.Pred): Term = pred match {
      case fsmodel.True => True()
      case fsmodel.False => False()
      case fsmodel.Not(a) => Not(evalPred(st, a))
      case fsmodel.And(a, b) => And(evalPred(st, a), evalPred(st, b))
      case fsmodel.Or(a, b) => Or(evalPred(st, a), evalPred(st, b))
      case fsmodel.TestFileState(p, fsmodel.IsDir) => Equals(st.paths(p), "IsDir")
      case fsmodel.TestFileState(p, fsmodel.DoesNotExist) => Equals(st.paths(p), "DoesNotExist")
      case fsmodel.TestFileState(p, fsmodel.IsFile) =>
        FunctionApplication("is-IsFile", Seq(st.paths(p)))
      case fsmodel.TestFileHash(p, h) => {
        val stat = st.paths(p)
        And(FunctionApplication("is-IsFile", Seq(stat)),
            (Equals(FunctionApplication("hash", Seq(stat)), hashToZ3(h.toList))))
      }
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
        val pre = And(Equals(st.paths(p), "DoesNotExist"),
          Equals(st.paths(p.getParent), "IsDir"))

        ST(Or(st.isErr, Not(pre)),
          st.paths + (p -> FunctionApplication("IsFile", Seq(hashToZ3(h.toList)))))
      }
      case fsmodel.Mkdir(p) => {
        val pre = And(Equals(st.paths(p), "DoesNotExist"),
          Equals(st.paths(p.getParent), "IsDir"))
        ST(Or(st.isErr, Not(pre)),
          st.paths + (p -> "IsDir"))
      }
      case fsmodel.Rm(p) => {
        val pre = FunctionApplication("is-IsFile", Seq(st.paths(p)))
        ST(Or(st.isErr, Not(pre)),
          st.paths + (p -> "DoesNotExist"))
      }
      case fsmodel.Cp(src, dst) => {
        val pre = And(FunctionApplication("is-IsFile", Seq(st.paths(src))),
          Equals(st.paths(dst.getParent), "IsDir"),
          Equals(st.paths(dst), "DoesNotExist"))
        ST(Or(st.isErr, Not(pre)),
          st.paths + (dst -> FunctionApplication("IsFile",
                                Seq(FunctionApplication("hash", Seq(st.paths(src)))))))
      }
    }

  def handleSexpr(reverseMap: Map[String, Path], reverseHash: Map[String, List[Byte]])(acc: Option[State], sexpr: SExpr): Option[State] =
    acc match {
      case None => None
      case Some(state) => {
        sexpr match {
          case DefineFun(FunDef(name, _, returnSort, body)) => {
            returnSort.id.symbol.name match {
              case "stat" => {
                val path = reverseMap.get(name.name).get
                body match {
                  case QualifiedIdentifier(Identifier(SSymbol("IsDir"), _), _) => Some(state + (path -> FDir))
                  //TODO(jcollard): Not sure how to deal with the file hash here. Is it important?
                  case FunctionApplication(QualifiedIdentifier(Identifier(SSymbol("IsFile"), _), _), List(hash)) => {
                    val data = reverseHash.getOrElse(hash.asInstanceOf[QualifiedIdentifier].id.symbol.name, List(42,42,42,42).map(x => x.toByte)).toArray
                    Some(state + (path -> FFile(data)))
                  }
                  case _ => Some(state)
                }
              }
              case "Bool" => if(name.name.startsWith("isErr") && body.asInstanceOf[QualifiedIdentifier].id.symbol.name.toBoolean) { None } else { Some(state) }
              case _ => throw new RuntimeException(s"Unexpected definition: $sexpr")
            }
          }
          case _ => Some(state)
        }
      }
    }


 def exprEqualsPrime(e1: fsmodel.Expr, e2: fsmodel.Expr): Option[Option[State]] = {
   try {
     process(Push(1))
     val st = freshST()
     val st1 = evalExpr(st, e1)
     val st2 = evalExpr(st, e2)


     process(Assert(Not(stEquals(st1, st2))))
     process(CheckSat()) match {
       case CheckSatStatus(SatStatus) => {
         val model: List[SExpr] = process(GetModel()).asInstanceOf[GetModelResponseSuccess].model
         val reverseMap = st.paths.map(x => (x._2.asInstanceOf[QualifiedIdentifier].id.symbol.name, x._1))
         val reverseHash = hashToZ3.map(x => (x._2.asInstanceOf[QualifiedIdentifier].id.symbol.name, x._1))
         Some(model.foldLeft(Some(Map()): Option[State])(handleSexpr(reverseMap, reverseHash)(_,_)))
       }
       case CheckSatStatus(UnsatStatus) => None
       case CheckSatStatus(UnknownStatus) => throw Unexpected("got unknown")
       case s => throw Unexpected(s"got $s from check-sat")
     }
   }
   finally {
     process(Pop(1))
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
          val c = freshName("choice")
          val b = process(DeclareConst(c, BoolSort()))
          ST(ITE(c, st1.isErr, st2.isErr),
            allPaths.map(p => p -> ITE(c, st1.paths(p),st2.paths(p))).toMap)
        })
      }
    }

    def isDeterministic(g: FileScriptGraph): Boolean = {
      val inST = freshST()
      val outST1 = evalGraph(inST, g)
      val outST2 = evalGraph(inST, g)
      process(Assert(Not(stEquals(outST1, outST2))))
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
