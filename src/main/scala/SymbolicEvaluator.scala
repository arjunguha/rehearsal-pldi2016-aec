package rehearsal

import FSEvaluator._
import smtlib._
import parser._
import Commands._
import Terms._
import theories.Core.{And => _, Or => _, _}
import scala.util.{Try, Success, Failure}
import CommandsResponses._
import java.nio.file.{Path, Paths}
import PuppetSyntax.{FSGraph}
import FSSyntax.{Block, Expr}
import rehearsal.{FSSyntax => F}
import rehearsal.Implicits._
import scalax.collection.Graph
import scalax.collection.GraphEdge.DiEdge
import scalax.collection.GraphPredef._
import scala.reflect.runtime.universe.TypeTag

object SymbolicEvaluator {

  def exprEquals(e1: F.Expr, e2: F.Expr): Option[State] = {
    val impl = new SymbolicEvaluatorImpl((e1.paths union e2.paths).toList,
      e1.hashes union e2.hashes, Set(), None)
    val result = impl.exprEquals(e1, e2)
    impl.free()
    result
  }

  def predEquals(a: F.Pred, b: F.Pred): Boolean = {
    val impl = new SymbolicEvaluatorImpl((a.readSet union b.readSet).toList, Set(), Set(), None)
    val result = impl.predEquals(a, b)
    impl.free()
    result
  }

   def mkImpl[K](g: FSGraph[K], logFile: Option[String]) = {
     val sets = Block(g.exprs.values.toSeq: _*).fileSets
     val ro = sets.reads -- sets.writes -- sets.dirs
    new SymbolicEvaluatorImpl(g.allPaths.toList,
      g.deps.nodes.map(n => g.exprs(n).hashes).reduce(_ union _),
      ro,
      logFile)
  }

  def isDeterministic(g: Graph[Expr, DiEdge]): Boolean = {
    isDeterministic(FSGraph(g.nodes.toList.map(x => x.value -> x.value).toMap, g))
  }

  def isDeterministicError(g: Graph[Expr, DiEdge]): Boolean = {
    isDeterministicError(FSGraph(g.nodes.toList.map(x => x.value -> x.value).toMap, g))
  }

  def isIdempotent(g: Graph[Expr, DiEdge]): Boolean = {
    isIdempotent(FSGraph(g.nodes.toList.map(x => x.value -> x.value).toMap, g))
  }

  def isDeterministic[K](g: FSGraph[K],  logFile: Option[String] = None): Boolean = {
    if (g.deps.nodes.size < 2) {
      return true
    }
    val impl = mkImpl(g, logFile)
    val result = impl.isDeterministic(g)
    impl.free()
    result
  }

  def isDeterministicError[K](g: FSGraph[K]): Boolean = {
    val impl = mkImpl(g, None)
    val result = impl.isDeterministicError(g)
    impl.free()
    result
  }
  def isIdempotent[K](g: FSGraph[K]): Boolean = {
    val impl = mkImpl(g, None)
    val result = impl.isIdempotent(g)
    impl.free()
    result
  }
}

case class ST(isErr: Term, paths: Map[Path, Term])

class SymbolicEvaluatorImpl(allPaths: List[Path],
                            hashes: Set[String],
                            readOnlyPaths: Set[Path],
                            logFile: Option[String]
                            ) extends com.typesafe.scalalogging.LazyLogging {
  import SMT._
  import SMT.Implicits._

  logger.info(s"Started with ${allPaths.size} paths, ${hashes.size} hashes, and ${readOnlyPaths.size} read-only paths")

  val writablePaths = allPaths.filterNot(p => readOnlyPaths.contains(p))

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

  val readOnlyMap = {
    val ids = readOnlyPaths.map(p => {
      val z = freshName("path")
      ((p, QualifiedIdentifier(Identifier(z))), DeclareConst(z, statSort))
    })
    val (paths, cmds) = ids.unzip
    for (c <- cmds) { eval(c) }
    paths.toMap
  }
  val (initState, _) = freshST()


  val reverseMap = initState.paths.map(x => (x._2.asInstanceOf[QualifiedIdentifier].id.symbol.name, x._1))
  val reverseHash = hashToZ3.map(x => (x._2.asInstanceOf[QualifiedIdentifier].id.symbol.name, x._1))

  // Ensures that all paths in st form a proper directory tree. If we assert
  // this for the input state and all operations preserve directory-tree-ness,
  // then there is no need to assert it for all states.
  def assertPathConsistency(st: ST): Unit = {
    val root = Paths.get("/")
    for (p <- allPaths) {
      if (p == root) {
        eval(Assert(FunctionApplication("is-IsDir", Seq(st.paths(p)))))
      }
      // If the parent of p is "/", there is no need to assert when "/" may
      // be a directory, due to the assertion above. In addition, if the
      // parent of p is not represented, there is no need for the assertion
      // either.
      else if (p.getParent != root && st.paths.contains(p.getParent)) {
        val pre = FunctionApplication("is-IsFile", Seq(st.paths(p))) ||
          FunctionApplication("is-IsDir", Seq(st.paths(p)))
        val post = FunctionApplication("is-IsDir", Seq(st.paths(p.getParent)))
        eval(Assert(Implies(pre, post)))
      }
    }
  }

  def freshST(): (ST, List[Command]) = {

    val ids = writablePaths.map(p => {
      val z = freshName("path")
      ((p, QualifiedIdentifier(Identifier(z))), DeclareConst(z, statSort))
    })
    val (paths, cmds) = ids.unzip
    val isErr = freshName("isErr")
    val commands = DeclareConst(isErr, BoolSort()) +: cmds
    commands.map(eval(_))
    (ST(QualifiedIdentifier(Identifier(isErr)), paths.toMap ++ readOnlyMap), commands)
  }

  def stEquals(st1: ST, st2: ST): Term = {
    (st1.isErr && st2.isErr) ||
      (Not(st1.isErr) && Not(st2.isErr) && And(writablePaths.map(p => Equals(st1.paths(p), st2.paths(p))): _*))
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
  }

  def predEquals(a: F.Pred, b: F.Pred): Boolean = smt.pushPop {
    val st = initState
     eval(Assert(Not(Equals(evalPred(st, a), evalPred(st, b)))))
    !smt.checkSat()
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
      for (p <- writablePaths) {
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
        writablePaths.map(p => (p, ite(b, st1.paths(p), st2.paths(p)))).toMap ++ readOnlyMap)
    }
    case F.CreateFile(p, h) => {
      assert(readOnlyPaths.contains(p) == false)
      val pre = Equals(st.paths(p), "DoesNotExist") && Equals(st.paths(p.getParent), "IsDir")
      ST(st.isErr || Not(pre),
        st.paths + (p -> FunctionApplication("IsFile", Seq(hashToZ3(h)))))
    }
    case F.Mkdir(p) => {
      assert(readOnlyPaths.contains(p) == false)
      val pre = Equals(st.paths(p), "DoesNotExist") && Equals(st.paths(p.getParent), "IsDir")
      ST(st.isErr || Not(pre),
        st.paths + (p -> "IsDir"))
    }
    case F.Rm(p) => {
      assert(readOnlyPaths.contains(p) == false)
      val descendants = st.paths.filter(p1 => p1._1 != p && p1._1.startsWith(p)).map(_._2).toSeq
      val pre = FunctionApplication("is-IsFile", Seq(st.paths(p))) ||
        (FunctionApplication("is-IsDir", Seq(st.paths(p))) &&
          And(descendants.map(p_ => Equals(p_, "DoesNotExist")) :_*))
      ST(st.isErr || Not(pre),
        st.paths + (p -> "DoesNotExist"))
    }
    case F.Cp(src, dst) => {
      assert(readOnlyPaths.contains(dst) == false)
      val pre = FunctionApplication("is-IsFile", Seq(st.paths(src))) &&
        Equals(st.paths(dst.getParent), "IsDir") &&
        Equals(st.paths(dst), "DoesNotExist")
      ST(st.isErr || Not(pre),
        st.paths + (dst -> FunctionApplication("IsFile",
          Seq(FunctionApplication("hash", Seq(st.paths(src)))))))
    }
  }

  def exprAsPred(st: ST, expr: F.Expr): Term = expr match {
    case F.Skip => True()
    case F.Error => False()
    case F.Seq(p, q) => exprAsPred(st, p) && exprAsPred(st, q)
    case F.If(a, e1, e2) => ite(evalPred(st, a), exprAsPred(st, e1), exprAsPred(st, e2))
    case _ => throw Unexpected(s"exprAsPred got $expr")
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

  def exprEquals(e1: F.Expr, e2: F.Expr): Option[State] = smt.pushPop {
    // TODO(arjun): Must rule out error as the initial state
    val st = initState
    assertPathConsistency(st)
    val st1 = evalExpr(st, e1)
    val st2 = evalExpr(st, e2)
    eval(Assert(Not(stEquals(st1, st2))))
    if (smt.checkSat()) {
      val model: List[SExpr] = eval(GetModel()).asInstanceOf[GetModelResponseSuccess].model
      Some(stateFromTerm(st).getOrElse(throw Unexpected("error for initial state")))
    }
    else {
      None
    }
  }

  // partition2(f, lst) = (lst1, lst2), such that f(x, y) holds for all distinct x and y in lst1.
  // Furthermore, lst1 ++ lst2 == lst without preserving ordering.
  // We assume that f is a commutative function.
  def partition2[A](f: (A, A) => Boolean, lst: List[A]): (List[A], List[A]) = {
    lst match {
      case Nil => (Nil, Nil)
      case rep :: others => {
        // Greedy: rep will be in the list
        val init = (List(rep), List[A]())
        others.foldLeft(init) {
          case ((lst1, lst2), y) => {
            if (lst1.forall(x => f(x, y))) {
              (y :: lst1, lst2)
            }
            else {
              (lst1, y :: lst2)
            }
          }
        }
      }
    }
  }

  def groupBy2[A](f: (A, A) => Boolean, lst: List[A]): List[List[A]] = partition2(f, lst) match {
    case (Nil, Nil) => Nil
    case (group, rest) => group :: groupBy2(f, rest)
  }

  // Greedily breaks a list of expressions into groups that commute with each other
  def commutingGroups[K](exprs: Map[K, Expr], lst: List[K]): List[List[K]] = {
    def f(m: K, n: K): Boolean = exprs(m).commutesWith(exprs(n))
    groupBy2(f, lst)
  }

  def evalGraph[K](st: ST, g: FSGraph[K]): ST = evalGraphAbort(st, g)((_, _) => false)

  case object AbortEarlyError extends RuntimeException("evalGraph aborted early")

  def predEarlyAbort(assertion: Expr, st1: ST, st2: ST): ST = {
    val isOK2 = exprAsPred(st2, assertion)
    smt.pushPop {
      val isOK1 = exprAsPred(st1, assertion)
      eval(Assert(Not(Equals(isOK1, isOK2))))
      if (smt.checkSat()) {
         throw AbortEarlyError
      }
    }
    ST(st2.isErr || Not(isOK2), st2.paths)
  }

  def evalGraphAbort[K](st: ST, g: FSGraph[K])(shouldAbort: (ST, ST) => Boolean): ST = {
    val fringe = g.deps.nodes.filter(_.inDegree == 0).toSet.map[K, Set[K]](_.value).toList
    val (assertions, nonAssertions) = fringe.partition(node => g.exprs(node).isEffectFree)
    val aExpr = Block(assertions.map(n => g.exprs(n)): _*)
    if (nonAssertions.length == 0) {
      evalExpr(st, aExpr)
    }
    else {
      val fringe1 = commutingGroups(g.exprs, nonAssertions)
      if (fringe1.length == 1) {
        val expr =  predEarlyAbort(aExpr, st, evalExpr(st, Block(fringe1.head.map(n => g.exprs(n)) : _*)))
        evalGraphAbort(expr, g.copy(deps = g.deps -- assertions -- fringe1.head))(shouldAbort)
      }
      else {
        logger.info(s"Choices: ${fringe1.length}")
        fringe1.toStream.map(p =>
            evalGraphAbort(predEarlyAbort(aExpr, st, evalExpr(st, Block(p.map(n => g.exprs(n)) : _*))),
                           g.copy(deps = g.deps -- assertions -- p))(shouldAbort)).reduce({ (st1: ST, st2: ST) =>
          if (shouldAbort(st1, st2)) {
            throw AbortEarlyError
          }
          val c = freshName("choice")
          val b = eval(DeclareConst(c, BoolSort()))
          ST(ite(c, st1.isErr, st2.isErr),
            writablePaths.map(p => p -> ite(c, st1.paths(p),st2.paths(p))).toMap ++ readOnlyMap)
        })
      }
    }
  }

  def isGraphDeterministic[K](st: ST, g: FSGraph[K]): (Term, ST) = {
    val fringe = g.deps.nodes.filter(_.inDegree == 0).toSet.map[K, Set[K]](_.value).toList
    if (fringe.length == 0) {
      (False(), st)
    }
    else {
      val fringe1 = commutingGroups(g.exprs, fringe)
      if (fringe1.length == 1) {
        val expr = evalExpr(st, Block(fringe1.head.map(n => g.exprs(n)) : _*))
        isGraphDeterministic(expr, g.copy(deps = g.deps -- fringe1.head))
      }
      else {
        logger.info(s"Choices: ${fringe1.length}")
        val lst = fringe1.map(nodes => isGraphDeterministic(evalExpr(st, Block(nodes.map(node => g.exprs(node)): _*)),
                                                            g.copy(deps = g.deps -- nodes)))
        lst.reduce((x: (Term, ST), y: (Term, ST)) => {
          val (pred1, st1) = x
          val (pred2, st2) = y
          val c = freshName("choice")
          val b = eval(DeclareConst(c, BoolSort()))
          (pred1 || pred2 || stNEq(st1, st2),
           ST(ite(c, st1.isErr, st2.isErr),
              writablePaths.map(p => p -> ite(c, st1.paths(p),st2.paths(p))).toMap ++ readOnlyMap))
        })
      }
    }
  }

  def stNEq(st1: ST, st2: ST): Term = {
    (st1.isErr && Not(st2.isErr)) ||
      (st2.isErr && Not(st1.isErr)) ||
      (Not(st1.isErr) && Not(st2.isErr) && Or(writablePaths.map(p => Not(Equals(st1.paths(p), st2.paths(p)))): _*))
  }

  def logDiff[A,B](m1: Map[A,B], m2: Map[A,B]): Unit = {
    val keys = m1.keySet ++ m2.keySet
    for (key <- keys) {
      (m1.get(key), m2.get(key)) match {
        case (None, None) => throw Unexpected("should have been in one")
        case (Some(x), None) => logger.info(s"$key -> $x REMOVED")
        case (None, Some(x)) => logger.info(s"$key -> $x ADDED")
        case (Some(x), Some(y)) => {
          if (x != y) {
            logger.info(s"$key -> $x -> $y CHANGED")
          }
        }
      }
    }
  }

  def diverged(inSt: ST)(st1: ST, st2: ST): Boolean = smt.pushPop {
    logger.info("Running divergence check.")
    eval(Assert(stNEq(st1, st2)))
    if (smt.checkSat()) {
      eval(GetModel())
      (stateFromTerm(inSt), stateFromTerm(st1), stateFromTerm(st2)) match {
        case (None, _, _) => throw Unexpected("bad model: initial state should not be error")
        case (Some(in), None, Some(out)) => {
          logger.info(s"On input\n$in\nthe program produces error or output\n$out")
          logDiff(in, out)
        }
        case (Some(in), Some(out), None) => {
          logger.info(s"On input\n$in\nthe program produces error or output\n$out")
          logDiff(in, out)
        }
        case (Some(in), Some(out1), Some(out2)) => {
          logger.info(s"On input\n$in\nthe program produces two possible outputs!")
        }
        case (Some(_), None, None) => throw Unexpected("bad model: both outputs are identical errors")
      }
      logger.info("Divergence check showed true.")
      true
    }
    else {
      logger.info("Divergence check showed false.")
      false
    }
  }
  def isIdempotent[K](e: Expr): Boolean = {
    val inST = initState
    val once = evalExpr(inST, e)
    val twice = evalExpr(once, e)
    eval(Assert(stNEq(once, twice)))
    if (smt.checkSat) {
      eval(GetModel())
      false
    }
    else {
      true
    }
  }

  def isIdempotent[K](g: FSGraph[K]): Boolean = smt.pushPop {
    assert(isDeterministic(g), "g is not deterministic; cannot determine idempotence")
    val nodes: List[K] = g.deps.topologicalSort()
    val exprs: List[Expr] = nodes.map(n => g.exprs.get(n).get)
    isIdempotent(exprs.foldRight(FSSyntax.Skip: Expr)((e, expr) => e >> expr))
  }

  def isDeterministic[K](g: FSGraph[K]): Boolean = smt.pushPop {
    val inST = initState
    logger.info(s"Generating constraints for a graph with ${g.exprs.size} nodes")
    val (pred, st) = isGraphDeterministic(inST, g)
    eval(Assert(pred))
    !smt.checkSat()
//    Try(evalGraphAbort(inST, g)(diverged(inST))) match {
//      case Failure(AbortEarlyError) => {
//        logger.info("Program is non-deterministic according to early error check.")
//        return false
//      }
//      case Failure(e) => throw e
//      case Success(st) => true
//    }
  }

  def isDeterministicError[K](g: FSGraph[K]): Boolean = smt.pushPop {
    val inST = initState
    assertPathConsistency(inST)
    val outST = evalGraph(inST, g)
    eval(Assert(Not(outST.isErr)))
    !smt.checkSat()
  }

  def free(): Unit = smt.free()

}

