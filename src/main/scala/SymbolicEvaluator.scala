package rehearsal

import FSEvaluator._
import smtlib._
import parser._
import Commands._
import Terms._
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
      e1.hashes union e2.hashes, Set())
    val result = impl.exprEquals(e1, e2)
    impl.free()
    result
  }

  def predEquals(a: F.Pred, b: F.Pred): Boolean = {
    val impl = new SymbolicEvaluatorImpl((a.readSet union b.readSet).toList, Set(), Set())
    val result = impl.predEquals(a, b)
    impl.free()
    result
  }


  def mkImpl(g: FSGraph) = {
     val sets = ESeq(g.exprs.values.toSeq: _*).fileSets
     val ro = sets.reads -- sets.writes -- sets.dirs
    new SymbolicEvaluatorImpl(g.allPaths.toList,
      g.deps.nodes.map(n => g.exprs(n).hashes).reduce(_ union _),
      ro)
  }


  def foo(g: Graph[Expr, DiEdge]): FSGraph = {
    val alist = g.nodes.map(n => n.value -> FSGraph.key())
    val m = alist.toMap

    FSGraph(alist.map({ case (k,v) => (v, k) }).toMap,
      Graph(g.edges.toList.map(edge => DiEdge(m(edge._1.value), m(edge._2.value))): _*))

  }
  def isDeterministic(g: Graph[Expr, DiEdge]): Boolean = {
    isDeterministic(foo(g))
  }

  def isDeterministicError(g: Graph[Expr, DiEdge]): Boolean = {
    isDeterministicError(foo(g))
  }

  def isIdempotent(g: Graph[Expr, DiEdge]): Boolean = {
    isIdempotent(foo(g))
  }

  def isDeterministic(g: FSGraph): Boolean = {
    g.toExecTree().isDeterministic()
  }

  def isDeterministicError(g: FSGraph): Boolean = {
    g.toExecTree().isDeterError()
  }

  def isIdempotent(g: FSGraph): Boolean = {
    val impl = mkImpl(g)
    val result = impl.isIdempotent(g)
    impl.free()
    result
  }
}

case class ST(isErr: Term, paths: Map[Path, Term])

class SymbolicEvaluatorImpl(allPaths: List[Path],
                            hashes: Set[String],
                            readOnlyPaths: Set[Path]
                            ) extends com.typesafe.scalalogging.LazyLogging {
  import SMT._
  import SMT.Implicits._

  logger.info(s"Started with ${allPaths.size} paths, ${hashes.size} hashes, and ${readOnlyPaths.size} read-only paths")

  val writablePaths = allPaths.filterNot(p => readOnlyPaths.contains(p))

  for (p <- writablePaths) {
    logger.debug(s"$p is writable")
  }
  for (p <- readOnlyPaths) {
    logger.debug(s"$p is read-only")
  }

  val smt = new SMT()
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
    eval(Assert(Forall(SortedVar(x, hashSort), Seq(),
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
  val initState = freshST()

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

  def freshST(): ST = {

    val ids = writablePaths.map(p => {
      val z = freshName("path")
      ((p, QualifiedIdentifier(Identifier(z))), DeclareConst(z, statSort))
    })
    val (paths, cmds) = ids.unzip
    val isErr = freshName("isErr")
    val commands = DeclareConst(isErr, BoolSort()) +: cmds
    commands.map(eval(_))
    ST(QualifiedIdentifier(Identifier(isErr)), paths.toMap ++ readOnlyMap)
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

  def ifST(b: Term, st1: ST, st2: ST): ST = {
    ST(ite(b, st1.isErr, st2.isErr),
      writablePaths.map(p => (p, ite(b, st1.paths(p), st2.paths(p)))).toMap ++ readOnlyMap)
  }

  def evalExpr(st: ST, expr: F.Expr): ST = expr match {
    case F.ESkip => st
    case F.EError => ST(True(), st.paths)
    case F.ESeq(p, q) => //evalExpr(evalExpr(st, p), q)
    {
      val stInter = evalExpr(st, p)
      val isErr = freshName("isErr")
      eval(DeclareConst(isErr, BoolSort()))
      val stInter1 = stInter.copy(isErr = isErr)
      eval(Assert(Equals(stInter.isErr, stInter1.isErr)))
      evalExpr(stInter1, q)
    }
    case F.EIf(a, e1, e2) => {
      val st1 = evalExpr(st, e1)
      val st2 = evalExpr(st, e2)
      val b = freshName("b")
      eval(DeclareConst(b, BoolSort()))
      eval(Assert(Equals(b, evalPred(st, a))))
      val isErr = freshName("isErr")
      eval(DeclareConst(isErr, BoolSort()))
      eval(Assert(Equals(isErr, ite(b, st1.isErr, st2.isErr))))
      ST(isErr,
        writablePaths.map(p => (p, ite(b, st1.paths(p), st2.paths(p)))).toMap ++ readOnlyMap)
    }
    case F.ECreateFile(p, h) => {
      assert(readOnlyPaths.contains(p) == false)
      val pre = Equals(st.paths(p), "DoesNotExist") && Equals(st.paths(p.getParent), "IsDir")
      ST(st.isErr ||  Not(pre),
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

  def isIdempotent(e: Expr): Boolean = {
    val inST = initState
    val once = evalExpr(inST, e)
    val twice = evalExpr(once, e)
    eval(Assert(Not(stEquals(once, twice))))
    if (smt.checkSat) {
      eval(GetModel())
      false
    }
    else {
      true
    }
  }

  def isIdempotent(g: FSGraph): Boolean = smt.pushPop {
    val nodes = g.deps.topologicalSort()
    val exprs: List[Expr] = nodes.map(n => g.exprs.get(n).get)
    isIdempotent(exprs.foldRight(FSSyntax.ESkip: Expr)((e, expr) => e >> expr))
  }

  def isDeter(execTree: ExecTree): Boolean = smt.pushPop {
    def evalTree(in: ST, t: ExecTree): Seq[(Expr, ST)] = t match {
      case ExecTree(es, Nil) => {
        val expr = FSSyntax.ESeq(es: _*)
        Seq((expr, evalExpr(in, expr)))
      }
      case ExecTree(es, children) => {
        val expr = FSSyntax.ESeq(es: _*)
        val out = evalExpr(in, expr)
        children.flatMap(t_ => evalTree(out, t_).map({ case (e, t) => (expr >> e, t) }))
      }
    }
    val in = initState
    assertPathConsistency(in)
    val outs = evalTree(in, execTree)
    outs match {
      case Nil => throw Unexpected("no possible final state: should never happen")
      case _ :: Nil => {
        logger.info("Trivially deterministic.")
        true
      }
      case out1 :: rest => {
        eval(Assert(Or(rest.map(out2 => Not(stEquals(out1._2, out2._2))): _*)))
        val nondet = smt.checkSat()
        !nondet
      }
    }
  }

  def alwaysError(expr: Expr) = smt.pushPop {
    val in = initState
    assertPathConsistency(in)
    val out = evalExpr(in, expr)
    eval(Assert(Not(out.isErr)))
    // Does there exist an input (in) that produces an output (out) that
    // is not the error state?
    !smt.checkSat()
  }

  def isDeterError(execTree: ExecTree): Boolean = smt.pushPop {
    isDeter(execTree) && alwaysError(execTree.exprs())
  }

  def free(): Unit = smt.free()

}


