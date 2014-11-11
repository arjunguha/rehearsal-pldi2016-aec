package equiv.ast

import java.nio.file.Path

sealed trait PathInfo
case object PathDoesNotExist extends PathInfo
case object PathIsFile extends PathInfo
case object PathIsDir extends PathInfo
case object PathIsLink extends PathInfo

trait TypedModel {
  // When using ScalaZ3, all these types will be Z3AST. But, the type
  // distinctions in this trait will help us keep our types straight.
  type S // The type used to represent states
  type B // The type used to represent boolean expressions
  type P // The type used to represent paths

  def trueB: B
  def falseB: B
  def andB(e1: B, e2: B): B
  def orB(e1: B, e2: B): B
  def notB(e: B): B
  def iffB(e1: B, e2: B): B
  def ifB(e1: B, e2: B, e3: B): B

  def exists(path: P, state: S): B
  def isDir(path: P, state: S): B
  def isFile(path: P, state: S): B
  def isLink(path: P, state: S): B

  def errState: S

  def mkState(): S

  def eqState(s1: S, s2: S): B

  def samePaths(s0: S, s1: S, paths: Map[Path, P]): B = {
    val clauses = paths.toSeq.map { case (_, p) =>
                    iffB(exists(p, s0), exists(p, s1))
                  }
    clauses.foldLeft(trueB)(andB)
  }

}

trait PredModel extends TypedModel {

  def eval(pred: Predicate, state: S, paths: Map[Path, P]): B = pred match {
    case True => trueB
    case False => falseB
    case Exists(p) => exists(paths(p), state)
    case IsDir(p) => isDir(paths(p), state)
    case IsRegularFile(p) => isFile(paths(p), state)
    case IsLink(p) => isLink(paths(p), state)
    case And(lhs, rhs) => andB(eval(lhs, state, paths), eval(rhs, state, paths))
    case Or(lhs, rhs) => orB(eval(lhs, state, paths), eval(rhs, state, paths))
    case Not(p) => notB(eval(p, state, paths))
  }

}


trait OptExprModel extends TypedModel with PredModel {

  import equiv.desugar._

  // We represent states as a state-variable (s0) and a map from
  // paths to their statically known states.
  //
  def evalOpt(expr: FSKATExpr,
              paths: Map[Path, P],
              s0: S,
              known: Map[Path, PathInfo]): Option[(B, S, Map[Path, PathInfo])] = expr match {
    case Id => Some((trueB, s0, known))
    case Err => None
    case MkDir(p) => (known.get(p.getParent), known.get(p)) match {
      // The parent is a directory and the child does not exist
      case (Some(PathIsDir), Some(PathDoesNotExist)) => {
        val path = paths(p)
        val parent = paths(p.getParent)
        Some((trueB,
              s0, // The output state is s0, but with a different known-set.
              known + (p -> PathIsDir)))
      }
      // p already exists in some state, so mkdir will error
      case (_, Some(_)) => None
      // In all other cases, return the most general expression. But, we can
      // do better by considering other state for the parent and path.
      case _ => {
        val s1 = mkState()
        val path = paths(p)
        val parent = paths(p.getParent)
        val b = ifB(exists(parent, s0),
            andB(exists(path, s1), samePaths(s0, s1, paths - p)),
            eqState(s0, errState))
        Some((b, s1, known + (p -> PathIsDir)))
      }
    }
    case Seqn(e1, e2) => for {
      (b1, s1, known1) <- evalOpt(e1, paths, s0, known)
      (b2, s2, known2) <- evalOpt(e2, paths, s1, known1)
    } yield (andB(b1, b2), s2, known2)
    case Opt(e1, e2) => (evalOpt(e1, paths, s0, known), evalOpt(e1, paths, s0, known)) match {
      case (None, None) => None
      case (Some(r), None) => Some(r) // e2 is statically eliminated
      case (None, Some(r)) => Some(r) // e1 is statically eliminated
      case (Some((b1, s1, known1)), Some((b2, s2, known2))) => {
        val s3 = mkState()
        Some((orB(andB(b1, reifyState(s1, paths, known1, s3)),
                  andB(b2, reifyState(s2, paths, known2, s3))),
              s3, Map()))
      }
    }
  }

  // Produces an expression that asserts that s1 is the same as s0, but with
  // the known paths' state set
  private def reifyState(s0: S,
                         paths: Map[Path, P],
                         known: Map[Path, PathInfo],
                         s1: S): B = {
    val clauses = known.toSeq.map { case (p, _) => exists(paths(p), s1) }
    andB(samePaths(s0, s1, paths -- known.keys),
         clauses.foldLeft(trueB)(andB))
  }

  def eval(expr: FSKATExpr, s0: S, paths: Map[Path, P]): (B, S) = {
    evalOpt(expr, paths, s0, Map()) match {
      case None => (eqState(s0, errState), s0)
      case Some((b, s1, known)) => {
        val s2 = mkState()
        (reifyState(s1, paths, known, s2), s2)
      }
    }
  }

}