package rehearsal

import Eval._
import smtlib._
import parser._
import Commands._
import Terms._
import theories.Core.{And => _, Or => _, _}
import CommandsResponses._
import java.nio.file.{Path, Paths}
import FSSyntax.{Block, Expr}
import rehearsal.{FSSyntax => F}

object SymbolicEvaluator2 {

   def exprEqualsSynth(precond: Set[State], e1: F.Expr, delta: F.Expr,
                       e2: F.Expr): Option[Option[State]] = {
    new SymbolicEvaluatorImpl((e1.paths union e2.paths union delta.paths).toList,
      e1.hashes union e2.hashes union delta.hashes, Some("wtf.smt")).exprEqualsSynth(precond, e1,delta, e2)
  }

  def exprEquals(e1: F.Expr, e2: F.Expr): Option[Option[State]] = {
    new SymbolicEvaluatorImpl((e1.paths union e2.paths).toList,
                    e1.hashes union e2.hashes, None).exprEquals(e1, e2)
  }
  def predEquals(a: F.Pred, b: F.Pred): Boolean = {
    new SymbolicEvaluatorImpl((a.readSet union b.readSet).toList, Set(), None).predEquals(a, b)
  }
  def isDeterministic(g: FileScriptGraph,
                      logFile: Option[String] = None): Boolean = {
    new SymbolicEvaluatorImpl(
      g.nodes.map(e => e.paths).reduce(_ union _).toList,
      g.nodes.map(_.hashes).reduce(_ union _),
      logFile
      ).isDeterministic(g)
  }
}

class SymbolicEvaluatorImpl(allPaths: List[Path],
                            hashes: Set[String],
                            logFile: Option[String]) extends com.typesafe.scalalogging.LazyLogging {
  import SMT._
  import SMT.Implicits._

  val smt = new SMT(logFile)
  import smt.eval

  eval(DeclareSort(SSymbol("hash"), 0))

  val hashSort = Sort(SimpleIdentifier(SSymbol("hash")))

  val hashToZ3: Map[String, Term] = hashes.toList.map(h => {
    val x = freshName("hash")
    eval(DeclareConst(x, hashSort))
    (h, QualifiedIdentifier(Identifier(x)))
  }).toMap

  if(hashToZ3.size != 0)  {
    val hashes = hashToZ3.values.toSeq
    eval(Assert(FunctionApplication("distinct", hashes)))
    val x = freshName("h")
    eval(Assert(ForAll(SortedVar(x, hashSort), Seq(),
                          Or(hashes.map(h => Equals(x, h)): _*))))
  }

  val termToHash: Map[Term, String] = hashToZ3.toList.map({ case (x,y) => (y, x) }).toMap

  // type stat = IsDir | DoesNotExist | IsFile of hash
  eval(DeclareDatatypes(Seq((SSymbol("stat"),
    Seq(Constructor(SSymbol("IsDir"), Seq()),
      Constructor(SSymbol("DoesNotExist"), Seq()),
      Constructor(SSymbol("IsFile"), Seq((SSymbol("hash"), hashSort))))))))

  val statSort = Sort(SimpleIdentifier(SSymbol("stat")))

  case class ST(isErr: Term, paths: Map[Path, Term])

  // Ensures that all paths in st form a proper directory tree. If we assert this for the input state
  // and all operations preserve directory-tree-ness, then there is no need to assert it for all states.
  def assertPathConsistency(st: ST): Unit = {
    for (p <- allPaths) {
      if (p == Paths.get("/")) {
        eval(Assert(FunctionApplication("is-IsDir", Seq(st.paths(p)))))
      }
      else {
        eval(Assert(Implies(FunctionApplication("is-IsFile", Seq(st.paths(p))) ||
                            FunctionApplication("is-IsDir", Seq(st.paths(p))),
                               FunctionApplication("is-IsDir", Seq(st.paths(p.getParent))))))
      }
    }
  }

  def buildPrecondition(st: ST, state: State): Term =
    st.paths.foldRight[Term](True())( { case ((p, t), pre: Term) =>
      state.get(p) match {
        case None => pre // DoesNotExist
        case Some(FDir) => pre && FunctionApplication("is-IsDir", Seq(t))
        case Some(FFile(hash)) => {
          hashToZ3.get(hash) match {
            case None => pre && FunctionApplication("is-IsFile", Seq(t))
            case Some(h) => Equals(t, FunctionApplication("IsFile", Seq(h)))
          }
        }
      }
    })

  def freshST(): ST = {
    val paths = allPaths.map(p => {
      val z = freshName("path")
      eval(DeclareConst(z, statSort))
      (p, QualifiedIdentifier(Identifier(z)))
    })
    val isErr = freshName("isErr")
    eval(DeclareConst(isErr, BoolSort()))
    ST(QualifiedIdentifier(Identifier(isErr)), paths.toMap)
  }

  def stEquals(st1: ST, st2: ST): Term = {
    (st1.isErr && st2.isErr) ||
      (Not(st1.isErr) && Not(st2.isErr) && And(allPaths.map(p => Equals(st1.paths(p), st2.paths(p))): _*))
  }

  def evalPred(st: ST, pred: F.Pred): Term = pred match {
    case F.True => True()
    case F.False => False()
    case F.Not(a) => Not(evalPred(st, a))
    case F.And(a, b) => evalPred(st, a) && evalPred(st, b)
    case F.Or(a, b) => evalPred(st, a) || evalPred(st, b)
    case F.TestFileState(p, F.IsDir) => Equals(st.paths(p), "IsDir")
    case F.TestFileState(p, F.DoesNotExist) => Equals(st.paths(p), "DoesNotExist")
    case F.TestFileState(p, F.IsFile) =>
      FunctionApplication("is-IsFile", Seq(st.paths(p)))
    //    case fsmodel.ITE(a, b, c) => ite(evalPred(st, a),
    //      evalPred(st, b),
    //      evalPred(st, c))
    case _ => throw NotImplemented(pred.toString)
  }

  def predEquals(a: F.Pred, b: F.Pred): Boolean = {
    try {
      eval(Push(1))
      val st = freshST()
      eval(Assert(Not(Equals(evalPred(st, a), evalPred(st, b)))))
      eval(CheckSat()) match {
        case CheckSatStatus(SatStatus) => {
          eval(GetModel())
          false
        }
        case CheckSatStatus(UnsatStatus) => true
        case CheckSatStatus(UnknownStatus) => throw Unexpected("got unknown")
        case s => throw Unexpected(s"got $s from check-sat")
      }
    }
    finally {
      eval(Pop(1))
    }
  }

  def ite(cond: Term, tru: Term, fls: Term): Term = {
    if (tru == fls) {
      tru
    }
    else {
      ITE(cond, tru, fls)
    }
  }

  def evalExpr(st: ST, expr: F.Expr): ST = expr match {
    case F.Skip => st
    case F.Error => ST(True(), st.paths)
    case F.Seq(p, q) => evalExpr(evalExpr(st, p), q)
    case F.If(a, e1, e2) => {
      val st1 = evalExpr(st, e1)
      val st2 = evalExpr(st, e2)
      val b = freshName("b")
      eval(DeclareConst(b, BoolSort()))
      eval(Assert(Equals(b, evalPred(st, a))))
      ST(ite(b, st1.isErr, st2.isErr),
        allPaths.map(p => (p, ite(b, st1.paths(p), st2.paths(p)))).toMap)
    }
    case F.CreateFile(p, h) => {
      val pre = Equals(st.paths(p), "DoesNotExist") && Equals(st.paths(p.getParent), "IsDir")
      ST(st.isErr || Not(pre),
        st.paths + (p -> FunctionApplication("IsFile", Seq(hashToZ3(h)))))
    }
    case F.Mkdir(p) => {
      val pre = Equals(st.paths(p), "DoesNotExist") && Equals(st.paths(p.getParent), "IsDir")
      ST(st.isErr || Not(pre),
        st.paths + (p -> "IsDir"))
    }
    case F.Rm(p) => {
      val descendants = st.paths.filter(p1 => p1._1 != p && p1._1.startsWith(p))
        .map(_._2).toSeq

      val pre = FunctionApplication("is-IsFile", Seq(st.paths(p))) ||
        (FunctionApplication("is-IsDir", Seq(st.paths(p))) &&
          And(descendants.map(p_ => Equals(p_, "DoesNotExist")) :_*))

      ST(st.isErr || Not(pre),
        st.paths + (p -> "DoesNotExist"))
    }
    case F.Cp(src, dst) => {
      val pre = FunctionApplication("is-IsFile", Seq(st.paths(src))) &&
        Equals(st.paths(dst.getParent), "IsDir") &&
        Equals(st.paths(dst), "DoesNotExist")
      ST(st.isErr || Not(pre),
        st.paths + (dst -> FunctionApplication("IsFile",
                              Seq(FunctionApplication("hash", Seq(st.paths(src)))))))
    }
  }


  def fstateFromTerm(term: Term): Option[Eval.FState] = term match {
    case QualifiedIdentifier(Identifier(SSymbol("IsDir"), Seq()), _) => Some(Eval.FDir)
    case FunctionApplication(QualifiedIdentifier(Identifier(SSymbol("IsFile"), _), _), Seq(h)) =>
      Some(Eval.FFile(termToHash.getOrElse(term, "<unknown>")))
    case QualifiedIdentifier(Identifier(SSymbol("DoesNotExist"), _), _) => None
    case _ => throw Unexpected(term.toString)

  }

  def stateFromTerm(st: ST): Option[State] = {
    val GetValueResponseSuccess(Seq((_,  isErr))) = eval(GetValue(st.isErr, Seq()))
    isErr match {
      case QualifiedIdentifier(Identifier(SSymbol("true"), Seq()), _) => None
      case QualifiedIdentifier(Identifier(SSymbol("false"), Seq()), _) => {
        val (paths, terms) = st.paths.toList.unzip
        val GetValueResponseSuccess(binds) = eval(GetValue(terms.head, terms.tail))
        Some(paths.zip(binds).map({ case (path, (_, t)) => fstateFromTerm(t).map(f => path -> f) }).flatten.toMap)
      }
      case _ => throw Unexpected("unexpected value for isErr")
    }
  }


  def handleSexpr(reverseMap: Map[String, Path], reverseHash: Map[String, String])(acc: Option[State], sexpr: SExpr): Option[State] =
    acc match {
      case None => None
      case Some(state) => {
        sexpr match {
          case DefineFun(FunDef(name, _, returnSort, body)) => {
            returnSort.id.symbol.name match {
              case "stat" => 
                reverseMap.get(name.name) match {
                  // Ignore all paths that are not the ones in ST
                  case None => Some(state)
                  case Some(path) =>
                    body match {
                      case QualifiedIdentifier(Identifier(SSymbol("IsDir"), _), _) => Some(state + (path -> FDir))
                      case FunctionApplication(QualifiedIdentifier(Identifier(SSymbol("IsFile"), _), _), List(hash)) => {
                        reverseHash.get(hash.asInstanceOf[QualifiedIdentifier].id.symbol.name) match {
                          case None => Some(state + (path -> FFile(s"unknown - ${hash.toString}")))
                          case Some(data) => Some(state + (path -> FFile(data)))
                        }
                      }
                      case QualifiedIdentifier(Identifier(SSymbol("DoesNotExist"), _), _) => Some(state)
                      case _ => throw Unexpected(s"Unexpected body: $body in sexpr: $sexpr")
                    }
                }

              case "Bool" => if(name.name.startsWith("isErr") && body.asInstanceOf[QualifiedIdentifier].id.symbol.name.toBoolean) { None } else { Some(state) }
              case "hash" => Some(state)
              case _ => throw Unexpected(s"Unexpected definition: $sexpr")
            }
          }
          
          case DeclareFun(_, _, Sort(SimpleIdentifier(SSymbol("hash")), _)) => Some(state)
          case ForAll(_,_, _) => Some(state)
          case _ => throw Unexpected(s"Unexpected sexpr: ${sexpr.getClass}")
        }
      }
    }

 def exprEqualsSynth(precond: Set[State], e1: F.Expr, delta: F.Expr,
                     e2: F.Expr): Option[Option[State]] = {
   try {
     eval(Push(1))
     val st = freshST()

     assertPathConsistency(st)
     logger.info(s"preconditions: ${precond.toSet.size}")

     precond.map(pre => eval(Assert(Not(buildPrecondition(st, pre)))))

     val stInter = evalExpr(st, e1)

     val st1 = evalExpr(stInter, delta)
     val st2 = evalExpr(st, e2)

     eval(Assert(Not(stEquals(stInter, st))))
     eval(Assert(Not(stEquals(st1, st2))))
     eval(CheckSat()) match {
       case CheckSatStatus(SatStatus) => {
         val model: List[SExpr] = eval(GetModel()).asInstanceOf[GetModelResponseSuccess].model
         val reverseMap = st.paths.map(x => (x._2.asInstanceOf[QualifiedIdentifier].id.symbol.name, x._1))
         val reverseHash = hashToZ3.map(x => (x._2.asInstanceOf[QualifiedIdentifier].id.symbol.name, x._1))
         logger.debug(model.toString)
         Some(model.foldLeft(Some(Map()): Option[State])(handleSexpr(reverseMap, reverseHash)(_,_)))
       }
       case CheckSatStatus(UnsatStatus) => None
       case CheckSatStatus(UnknownStatus) => throw Unexpected("got unknown")
       case s => throw Unexpected(s"got $s from check-sat")
     }
   }
   finally {
     eval(Pop(1))
   }
 }


 def exprEquals(e1: F.Expr, e2: F.Expr): Option[Option[State]] = {
   try {
     eval(Push(1))
     val st = freshST()
     val st1 = evalExpr(st, e1)
     val st2 = evalExpr(st, e2)

     eval(Assert(Not(stEquals(st1, st2))))
     eval(CheckSat()) match {
       case CheckSatStatus(SatStatus) => {
         val model: List[SExpr] = eval(GetModel()).asInstanceOf[GetModelResponseSuccess].model
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
     eval(Pop(1))
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
          val b = eval(DeclareConst(c, BoolSort()))
          ST(ite(c, st1.isErr, st2.isErr),
            allPaths.map(p => p -> ite(c, st1.paths(p),st2.paths(p))).toMap)
        })
      }
    }

    def isDeterministic(g: FileScriptGraph): Boolean = {
      val inST = freshST()
      val outST1 = evalGraph(inST, g)
      val outST2 = evalGraph(inST, g)
      eval(Assert(Not(stEquals(outST1, outST2))))
     // assertHashCardinality()
      eval(CheckSat()) match {
        case CheckSatStatus(SatStatus) => {
          eval(GetModel())
          false
        }
        case CheckSatStatus(UnsatStatus) => true
        case CheckSatStatus(UnknownStatus) => throw new RuntimeException("got unknown")
        case s => throw Unexpected(s"got $s from check-sat")
      }

    }

}
