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
  def impliesB(e1: B, e2: B): B

  def exists(path: P, state: S): B
  def isDir(path: P, state: S): B
  def isFile(path: P, state: S): B
  def isLink(path: P, state: S): B

  def isError(state: S): B

  def mkState(): S

  def eqState(s1: S, s2: S): B

  def samePaths(s0: S, s1: S, paths: Map[Path, P]): B = {
    val clauses = paths.toSeq.map { case (_, p) =>
                    iffB(exists(p, s0), exists(p, s1))
                  }
    clauses.foldLeft(trueB)(andB)
  }

  def seqError(s0: S, s1: S): B = impliesB(isError(s0), isError(s1))

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

trait ExprModel extends TypedModel with PredModel {

 import equiv.desugar._

  def eval(expr: FSKATExpr, paths: Map[Path, P], s0: S): (B, S) = expr match {
    case Id => (trueB, s0)
    case Err => {
      val s1 = mkState()
      (isError(s1), s1)
    }
    case MkDir(p) => {
      val s1 = mkState()
      val path = paths(p)
      val parent = paths(p.getParent)
      val b = ifB(andB(exists(parent, s0), notB(exists(path, s0))),
                  andB(exists(path, s1), samePaths(s0, s1, paths - p)),
                  isError(s1))
      (b, s1)
    }
    case Seqn(e1, e2) => {
      val (b1, s1) = eval(e1, paths, s0)
      val (b2, s2) = eval(e2, paths, s1)
      (andB(andB(andB(b1, b2),
                 impliesB(isError(s0), isError(s1))),
            impliesB(isError(s1), isError(s2))),
       s2)
    }
    case Opt(e1, e2) => {
      val (b1, s1) = eval(e1, paths, s0)
      val (b2, s2) = eval(e2, paths, s0)
      val s3 = mkState()
      val b = orB(andB(b1, eqState(s1, s3)), andB(b2, eqState(s2, s3)))
      val errB = andB(impliesB(isError(s0), isError(s1)),
                      andB(impliesB(isError(s0), isError(s2)),
                           impliesB(orB(isError(s1), isError(s2)), isError(s3))))
      (andB(b, errB), s3)
    }
  }
}

trait OptExprModel extends TypedModel with PredModel {

  import equiv.desugar._

  case class State(s: S, paths: Map[Path, PathInfo], error: Option[Boolean])

  // We represent states as a state-variable (s0) and a map from
  // paths to their statically known states.
  //
  def evalOpt(expr: FSKATExpr,
              paths: Map[Path, P],
              s0: State) : (B, State) = expr match {
    case Id => (trueB, s0)
    case Err => {
      val s1 = mkState()
      (trueB, State(s1, Map(), Some(true)))
    }
    case MkDir(p) => (s0.paths.get(p.getParent), s0.paths.get(p)) match {
      // The parent is a directory and the child does not exist
      case (Some(PathIsDir), Some(PathDoesNotExist)) => {
        val path = paths(p)
        val parent = paths(p.getParent)
        (trueB, State(s0.s, s0.paths + (p -> PathIsDir), s0.error))
      }
      // p already exists in some state, so mkdir will error
      // case (_, Some(_)) => (trueB, State(s0.s, s0.paths, Some(true)))
      // In all other cases, return the most general expression. But, we can
      // do better by considering other state for the parent and path.
      case _ => {
        val s00 = mkState()
        val b0 = reifyState(s0, paths, s00)
        val s1 = mkState()
        val path = paths(p)
        val parent = paths(p.getParent)
        val b = ifB(andB(exists(parent, s00), notB(exists(path, s00))),
                    andB(seqError(s00, s1), andB(exists(path, s1), samePaths(s00, s1, paths - p))),
                    isError(s1))
        (andB(b0, b),
         State(s1, Map(), None))
      }
    }
    case Seqn(e1, e2) => {
      val (b1, s1) = evalOpt(e1, paths, s0)
      val (b2, s2) = evalOpt(e2, paths, s1)
      (andB(b1, b2), s2)
    }
    case Opt(e1, e2) => {
      val (b1, s1) = evalOpt(e1, paths, s0)
      val (b2, s2) = evalOpt(e2, paths, s0)
      val s3 = mkState()
      val b = orB(andB(b1, reifyState(s1, paths, s3)),
                  andB(b2, reifyState(s2, paths, s3)))
      (b, State(s3, Map(), None))
    }
  }

  // Produces an expression that asserts that s1 is the same as s0, but with
  // the known paths' state set
  private def reifyState(s0: State, paths: Map[Path, P], s1: S): B = {
    val clauses = s0.paths.toSeq.map { case (p, _) => exists(paths(p), s1) }
    andB(andB(clauses.foldLeft(trueB)(andB), samePaths(s0.s, s1, paths -- s0.paths.keys)),
         s0.error match {
          case Some(true) => isError(s1) // seqError(s0.s, s1)
          case Some(false) => notB(isError(s1))
          case None => seqError(s0.s, s1)
        })
  }

  val rootPath = java.nio.file.Paths.get("/")
  def concretePaths[A](paths: Map[Path, A]): Map[Path, PathInfo] = {
    paths.map { case (path, _) => if (path == rootPath) (path, PathIsDir) else (path, PathDoesNotExist) }
    //Map()
  }

  def eval(expr: FSKATExpr, paths: Map[Path, P], s0: S): (B, S) = {
    val (b, s1) = evalOpt(expr, paths, State(s0, concretePaths(paths), Some(false)))
    val s2 = mkState()
    (andB(b, reifyState(s1, paths, s2)), s2)
  }

}