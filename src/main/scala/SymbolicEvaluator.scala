package rehearsal

import FSEvaluator._
import smtlib._
import parser._
import Commands._
import Terms._
import theories.Core.{And => _, Or => _, _}
import CommandsResponses._
import java.nio.file.{Path, Paths}
import FSSyntax.{Block, Expr}
import rehearsal.{FSSyntax => F}
import scalax.collection.GraphPredef._

object SymbolicEvaluator {

  def exprEquals(e1: F.Expr, e2: F.Expr): Option[Option[State]] = {
    val impl = new SymbolicEvaluatorImpl((e1.paths union e2.paths).toList,
      e1.hashes union e2.hashes, None)
    val result = impl.exprEquals(e1, e2)
    impl.free()
    result
  }

  def predEquals(a: F.Pred, b: F.Pred): Boolean = {
    val impl = new SymbolicEvaluatorImpl((a.readSet union b.readSet).toList, Set(), None)
    val result = impl.predEquals(a, b)
    impl.free()
    result
  }
  def isDeterministic(g: FileScriptGraph,
                      logFile: Option[String] = None): Boolean = {
    if (g.nodes.size < 2) {
      return true
    }
    val impl = new SymbolicEvaluatorImpl(
      g.nodes.map(e => e.paths).reduce(_ union _).toList,
      g.nodes.map(_.hashes).reduce(_ union _),
      logFile
    )
    val result = impl.isDeterministic(g)
    impl.free()
    result
  }
  def isDeterministicError(g: FileScriptGraph): Boolean = {
    val impl = new SymbolicEvaluatorImpl(
      g.nodes.map(e => e.paths).reduce(_ union _).toList,
      g.nodes.map(_.hashes).reduce(_ union _),
      None
    )
    val result = impl.isDeterministicError(g)
    impl.free()
    result
  }
}

case class ST(isErr: Term, paths: Map[Path, Term])

sealed trait Precond {

  def apply(st: ST): Term
}

case class PrecondAtom(files: Map[Path, Either[Term, Term => Term]]) extends Precond {

  import smtlib.parser.Terms._
  import SMT._
  override def toString() = files.toList.map({ case (p, t) => (p, t match {
    case Left(t) => t
    case Right(t) => t(QualifiedIdentifier(Identifier(SSymbol("_"), Seq()), None))
  }) }).toMap.toString

  def restrictPath(tup: (Path, Term)) = {
    val (p, x) = tup
    files(p) match {
      case Left(term) => Equals(x, term)
      case Right(f) => f(x)
    }
  }

  def apply(st: ST): Term = {
    Not(And(Equals(st.isErr, False()),  And(st.paths.toList.map(restrictPath): _*)))
  }

}

case class PrecondAnd(p1: Precond, p2: Precond) extends Precond {
  import SMT._
  def apply(st: ST): Term = And(p1(st), p2(st))
}

case object PrecondTrue extends Precond {
  import smtlib.parser.Terms._
  def apply(st: ST): Term = True()
}

class SymbolicEvaluatorImpl(allPaths: List[Path],
                            hashes: Set[String],
                            logFile: Option[String]) extends com.typesafe.scalalogging.LazyLogging {
  import SMT._
  import SMT.Implicits._

  logger.info(s"Started with ${allPaths.size} paths and ${hashes.size} hashes")
  logger.info(allPaths.toString)

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

  val (initState, _) = freshST()
  val reverseMap = initState.paths.map(x => (x._2.asInstanceOf[QualifiedIdentifier].id.symbol.name, x._1))
  val reverseHash = hashToZ3.map(x => (x._2.asInstanceOf[QualifiedIdentifier].id.symbol.name, x._1))


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
            case Some(h) => pre && Equals(t, FunctionApplication("IsFile", Seq(h)))
          }
        }
      }
    })

  def buildST(precond: Precond): Option[ST] = {
    val (st, _) = freshST()
    eval(Assert(precond(st)))
    smt.checkSat() match {
      case SatStatus => {
        val _ = smt.getModel()
        Some(st)
      }
      case UnsatStatus => None
      case UnknownStatus => throw Unexpected("got unknown")
    }
  }

  def freshST(): (ST, List[Command]) = {
    val ids = allPaths.map(p => {
      val z = freshName("path")
      ((p, QualifiedIdentifier(Identifier(z))), DeclareConst(z, statSort))
    })
    val (paths, cmds) = ids.unzip
    val isErr = freshName("isErr")
    val commands = DeclareConst(isErr, BoolSort()) +: cmds
    commands.map(eval(_))
    (ST(QualifiedIdentifier(Identifier(isErr)), paths.toMap), commands)
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
      val st = initState
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
    case F.Seq(p, q) => {
      val stInter = evalExpr(st, p)
      val (stInter1, _) = freshST()
      eval(Assert(Equals(stInter.isErr, stInter1.isErr)))
      for (p <- allPaths) {
        eval(Assert(Equals(stInter.paths(p), stInter1.paths(p))))
      }
      evalExpr(stInter1, q)
    }
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
      val descendants = st.paths.filter(p1 => p1._1 != p && p1._1.startsWith(p)).map(_._2).toSeq
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

  def fstateFromTerm(term: Term): Option[FSEvaluator.FState] = term match {
    case QualifiedIdentifier(Identifier(SSymbol("IsDir"), _), _) => Some(FSEvaluator.FDir)
    case FunctionApplication(QualifiedIdentifier(Identifier(SSymbol("IsFile"), _), _), Seq(h)) =>
      Some(FSEvaluator.FFile(termToHash.getOrElse(term, "<unknown>")))
    case QualifiedIdentifier(Identifier(SSymbol("DoesNotExist"), _), _) => None
    case _ => throw Unexpected(term.toString)

  }

  def stateFromTerm(st: ST): Option[State] = {
    val Seq((_, isErr)) = smt.getValue(Seq(st.isErr))
    isErr match {
      case QualifiedIdentifier(Identifier(SSymbol("true"), Seq()), _) => None
      case QualifiedIdentifier(Identifier(SSymbol("false"), Seq()), _) => {
        val (paths, terms) = st.paths.toList.unzip
        val pathVals = smt.getValue(terms).map(_._2)
        // Filtering out the Nones with .flatten
        Some(paths.zip(pathVals).map({ case (path, t) => fstateFromTerm(t).map(f => path -> f) }).flatten.toMap)
      }
      case _ => throw Unexpected("unexpected value for isErr")
    }
  }


  def predFromTerm(st: ST): Precond = {
    val Seq((_, isErr)) = smt.getValue(Seq(st.isErr))
    isErr match {
      case QualifiedIdentifier(Identifier(SSymbol("true"), Seq()), _) => throw Unexpected("counterexample is error")
      case QualifiedIdentifier(Identifier(SSymbol("false"), Seq()), _) => {
        PrecondAtom(st.paths.toList.map({
          case (p, term) => smt.getValue(Seq(term)).head._2 match {
            case FunctionApplication(QualifiedIdentifier(Identifier(SSymbol("IsFile"), _), _), Seq(h))
              if (termToHash.contains(h) == false) => p -> Right((y: Term) =>  FunctionApplication("is-IsFile", Seq(y)))
            case x => p -> Left(x)
          }
        }).toMap)
      }
      case _ => throw Unexpected("unexpected value for isErr")
    }
  }

  // Produces None if this formula is valid:
  //
  //  forall s . precond(s) => [[e1; delta]] s == [[e2] s
  //
  // This is equivalent to proving this formula unsatisfiable:
  //
  // exists s . precond(s) && [[e1; delta]] s != [[e2] s
  //
  // If the formula is invalid, produces Some((pred, cex)) such that:
  //
  // - [[e1; delta]] cex != [[e2]] cex
  // - forall s . pred(s) => [[e1; delta]] s != [[e2]] s
  def verifyUpdate(precond: Precond, e1: F.Expr, delta: F.Expr, e2: F.Expr): Option[(State, Precond)] = smt.pushPop {
    //logger.info(s"verifyUpdate($precond, $delta)")
    val st0 = initState
    assertPathConsistency(st0)
    eval(Assert(precond(st0)))

    val stInter = evalExpr(st0, e1)
    val st1 = evalExpr(stInter, delta)
    val st2 = evalExpr(st0, e2)

    // TODO(arjun): This asserts that e1 has "some effect". Are we actually relying on it? We need to either
    // remove this or justify it.
    eval(Assert(Not(stEquals(stInter, st0))))

    eval(Assert(Not(stEquals(st1, st2))))

    smt.checkSat() match {
      case SatStatus => {
        val _ = smt.getModel()
        val newPrecond = predFromTerm(st0)
        logger.info(s"precondition: $newPrecond")
        Some((stateFromTerm(st0).getOrElse(throw Unexpected("state is an error")), newPrecond))
      }
      case UnsatStatus => None
      case UnknownStatus => throw Unexpected("got unknown")
    }
  }

  def exprEquals(e1: F.Expr, e2: F.Expr): Option[Option[State]] = {
    try {
      eval(Push(1))
      // TODO(arjun): Must rule out error as the initial state
      val st = initState
      val st1 = evalExpr(st, e1)
      val st2 = evalExpr(st, e2)

      eval(Assert(Not(stEquals(st1, st2))))
      eval(CheckSat()) match {
        case CheckSatStatus(SatStatus) => {
          val model: List[SExpr] = eval(GetModel()).asInstanceOf[GetModelResponseSuccess].model
          Some(Some(stateFromTerm(st).getOrElse(throw Unexpected("error for initial state"))))
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

  // Greedily breaks a list of expressions into groups that commute with each other
  def commutingGroups(lst: List[Expr]): List[List[Expr]] = {
    lst match {
      case Nil => Nil
      case x :: xs => {
        val (others, commutes) = xs.foldLeft((List[Expr](), List(x))) {
          case ((others, commutes), y) => {
            if (commutes.forall(_.commutesWith(y))) {
              (others, y :: commutes)
            }
            else {
              (y :: others, commutes)
            }
          }
        }
        commutes :: commutingGroups(others)
      }
    }
  }

  def evalGraph(st: ST, g: FileScriptGraph): ST = {
    val fringe = g.nodes.filter(_.inDegree == 0).toList
    if (fringe.length == 0) {
      st
    }
    else {
      val fringe1 = commutingGroups(fringe.map[Expr, List[Expr]](x => x))
      if (fringe1.length == 1) {
        evalExpr(st, Block(fringe1.head : _*))
      }
      else {
        fringe1.map(p => evalGraph(evalExpr(st, Block(p : _*)), g -- p)).reduce({ (st1: ST, st2: ST) =>
          val c = freshName("choice")
          val b = eval(DeclareConst(c, BoolSort()))
          ST(ite(c, st1.isErr, st2.isErr),
            allPaths.map(p => p -> ite(c, st1.paths(p),st2.paths(p))).toMap)
        })
      }
    }
  }

  def stNEq(st1: ST, st2: ST): Term = {
    (st1.isErr && Not(st2.isErr)) ||
      (st2.isErr && Not(st1.isErr)) ||
      (Not(st1.isErr) && Not(st2.isErr) && Or(allPaths.map(p => Not(Equals(st1.paths(p), st2.paths(p)))): _*))
  }

  def isDeterministic(g: FileScriptGraph): Boolean = {
    val inST = initState
    logger.info(s"Generating constraints for a graph with ${g.nodes.size} nodes")
    val outST1 = evalGraph(inST, g)
    val outST2 = evalGraph(inST, g)
    eval(Assert(stNEq(outST1, outST2)))
    logger.info("Checking satisfiability")
    eval(CheckSat()) match {
      case CheckSatStatus(SatStatus) => {
        logger.info("program is non-deterministic")
        eval(GetModel())
        (stateFromTerm(inST), stateFromTerm(outST1), stateFromTerm(outST2)) match {
          case (None, _, _) => throw Unexpected("bad model: initial state should not be error")
          case (Some(in), None, Some(out)) => logger.info(s"On input\n$in\nthe program produces error or output\n$out")
          case (Some(in), Some(out), None) => logger.info(s"On input\n$in\nthe program produces error or output\n$out")
          case (Some(in), Some(out1), Some(out2)) => {
            logger.info(s"On input\n$in\nthe program produces two possible outputs!")
          }
          case (Some(_), None, None) => throw Unexpected("bad model: both outputs are identical errors")
        }
        false
      }
      case CheckSatStatus(UnsatStatus) => true
      case CheckSatStatus(UnknownStatus) => throw new RuntimeException("got unknown")
      case s => throw Unexpected(s"got $s from check-sat")
    }

  }

  def isDeterministicError(g: FileScriptGraph): Boolean = {
    val inST = initState
    val outST = evalGraph(inST, g)
    eval(Assert(Not(outST.isErr)))
    eval(CheckSat()) match {
      case CheckSatStatus(SatStatus) => false
      case CheckSatStatus(UnsatStatus) => true
      case CheckSatStatus(UnknownStatus) => throw new RuntimeException("got unknown")
      case s => throw Unexpected(s"got $s from check-sat")
    }
    
  }
  
  def free(): Unit = smt.free()

}

