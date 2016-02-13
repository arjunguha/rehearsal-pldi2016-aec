package rehearsal

import FSEvaluator._
import smtlib._
import parser._
import Commands._
import Terms._
import theories.Core.{And => _, Or => _, _}
import scala.util.{Try, Success, Failure}
import CommandsResponses._
import java.nio.file.{Paths}
import FSSyntax.{ESeq, Expr}
import rehearsal.{FSSyntax => F}
import rehearsal.Implicits._
import scalax.collection.Graph
import scalax.collection.GraphEdge.DiEdge

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
     val sets = ESeq(g.exprs.values.toSeq: _*).fileSets
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

  def isDeterministicWithTimeout[K](g: FSGraph[K], timeout: Int,  logFile: Option[String] = None): Option[Boolean] = {
    if (g.deps.nodes.size < 2) {
      return Some(true)
    }
    val impl = mkImpl(g, logFile)
    new Thread(new Runnable {
      def run() {
        Thread.sleep(timeout * 1000)
        impl.free()
      }
    }).run
    Try(impl.isDeterministic(g)) match {
      case Success(res) => impl.free(); Some(res)
      case Failure(e) => None
    }
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

  for (p <- writablePaths) {
    logger.info(s"$p is writable")
  }
  for (p <- readOnlyPaths) {
    logger.info(s"$p is read-only")
  }

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

  // TODO(arjun): What is the point of returning these commands?
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
    case F.PTrue => True()
    case F.PFalse => False()
    case F.PNot(a) => Not(evalPred(st, a))
    case F.PAnd(a, b) => evalPred(st, a) && evalPred(st, b)
    case F.POr(a, b) => evalPred(st, a) || evalPred(st, b)
    case F.PTestFileState(p, F.IsDir) => Equals(st.paths(p), "IsDir")
    case F.PTestFileState(p, F.DoesNotExist) => Equals(st.paths(p), "DoesNotExist")
    case F.PTestFileState(p, F.IsFile) =>
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

  def ifST(b: Term, st1: ST, st2: ST): ST = {
    ST(ite(b, st1.isErr, st2.isErr),
      writablePaths.map(p => (p, ite(b, st1.paths(p), st2.paths(p)))).toMap ++ readOnlyMap)
  }

  def evalExpr(st: ST, expr: F.Expr): ST = expr match {
    case F.ESkip => st
    case F.EError => ST(True(), st.paths)
    case F.ESeq(p, q) => {
      val stInter = evalExpr(st, p)
      val (stInter1, _) = freshST()
      eval(Assert(Equals(stInter.isErr, stInter1.isErr)))
      for (p <- writablePaths) {
        eval(Assert(Equals(stInter.paths(p), stInter1.paths(p))))
      }
      evalExpr(stInter1, q)
    }
    case F.EIf(a, e1, e2) => {
      val st1 = evalExpr(st, e1)
      val st2 = evalExpr(st, e2)
      val b = freshName("b")
      eval(DeclareConst(b, BoolSort()))
      eval(Assert(Equals(b, evalPred(st, a))))
      ST(ite(b, st1.isErr, st2.isErr),
        writablePaths.map(p => (p, ite(b, st1.paths(p), st2.paths(p)))).toMap ++ readOnlyMap)
    }
    case F.ECreateFile(p, h) => {
      assert(readOnlyPaths.contains(p) == false)
      val pre = Equals(st.paths(p), "DoesNotExist") && Equals(st.paths(p.getParent), "IsDir")
      ST(st.isErr || Not(pre),
        st.paths + (p -> FunctionApplication("IsFile", Seq(hashToZ3(h)))))
    }
    case F.EMkdir(p) => {
      assert(readOnlyPaths.contains(p) == false,
        s"Mkdir($p) found, but path is read-only")
      val pre = Equals(st.paths(p), "DoesNotExist") && Equals(st.paths(p.getParent), "IsDir")
      ST(st.isErr || Not(pre),
        st.paths + (p -> "IsDir"))
    }
    case F.ERm(p) => {
      assert(readOnlyPaths.contains(p) == false)
      val descendants = st.paths.filter(p1 => p1._1 != p && p1._1.startsWith(p)).map(_._2).toSeq
      val pre = FunctionApplication("is-IsFile", Seq(st.paths(p))) ||
        (FunctionApplication("is-IsDir", Seq(st.paths(p))) &&
          And(descendants.map(p_ => Equals(p_, "DoesNotExist")) :_*))
      ST(st.isErr || Not(pre),
        st.paths + (p -> "DoesNotExist"))
    }
    case F.ECp(src, dst) => {
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
    case F.ESkip => True()
    case F.EError => False()
    case F.ESeq(p, q) => exprAsPred(st, p) && exprAsPred(st, q)
    case F.EIf(a, e1, e2) => ite(evalPred(st, a), exprAsPred(st, e1), exprAsPred(st, e2))
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
    def f(m: K, n: K): Boolean = {
      val b = exprs(m).commutesWith(exprs(n))
      if (!b) {
        logger.info(s"$m.commutesWith($n) was false")
      }
      b
    }
    groupBy2(f, lst)
  }

  def stSeq(init: ST)(rest: List[(ST, ST)]): (Term, ST) = {
    def loop(curr: ST, lst: List[(ST, ST)]): (Term, ST) = lst match {
      case Nil => (True(), curr)
      case (inST, outST) :: tail => {
        val term1 = stEquals(curr, inST)
        val (term2, st) = loop(outST, tail)
        (term1 && term2, st)
      }
    }
    loop(init, rest)
  }

  def evalGraph[K](st: ST, g: FSGraph[K]): ST = {
    logger.info(s"evalGraph applied to a graph with ${g.deps.nodes.size} nodes")

    val fringe = g.deps.nodes.filter(_.inDegree == 0).toList.map(_.value)
    if (fringe.isEmpty) {
      return st
    }

    val rels = commutingGroups(g.exprs, fringe)
      .map(nodes => {
        logger.info(s"Group $nodes")
        ESeq(nodes.map(n => g.exprs(n)): _*)
      })
      .map(expr => {
        val (inST, _) = freshST()
        (inST, evalExpr(inST, expr))
      })
      .permutations
      .map(stSeq(st))
      .toList
      .reverse

    if (rels.length == 1) {
      val (term, st) = rels.head
      eval(Assert(term))
      return evalGraph(st, g.copy(deps = g.deps -- fringe))
    }
    logger.info(s"${rels.length} commuting groups")

    // TODO(arjun): Need to print the groups (node names) to understand
    // why things don't commute

    val (term, outST) = rels.reduce {
      (lhs: (Term, ST), rhs: (Term, ST)) => {
        val (term1, st1) = lhs
        val (term2, st2) = rhs
        val c = freshName("choice")
        eval(DeclareConst(c, BoolSort()))
        (ITE(c, term1, term2), ifST(c, st1, st2))
      }
    }
    eval(Assert(term))
    evalGraph(outST, g.copy(deps = g.deps -- fringe))
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
    isIdempotent(exprs.foldRight(FSSyntax.ESkip: Expr)((e, expr) => e >> expr))
  }

  def isDeterministic[K](g: FSGraph[K]): Boolean = smt.pushPop {
    val inST = initState
    assertPathConsistency(inST)
    logger.info(s"Generating constraints for a graph with ${g.exprs.size} nodes")
    val outST1 = evalGraph(inST, g)
    val outST2 = evalGraph(inST, g)
    eval(Assert(Not(stEquals(outST1, outST2))))
    val nondet = smt.checkSat()
    if (nondet) {
      eval(GetModel())
      (stateFromTerm(inST), stateFromTerm(outST1), stateFromTerm(outST2)) match {
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
          logger.info(out1.toString)
          logger.info(out2.toString)

        }
        case (Some(_), None, None) => throw Unexpected("bad model: both outputs are identical errors")
      }
    }
    !nondet
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


