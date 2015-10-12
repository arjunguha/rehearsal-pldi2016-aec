package rehearsal

object FSEvaluator {

  import FSSyntax._
  import java.nio.file.Path

  type S = Option[State]

  sealed trait FState
  case object FDir extends FState
  case class FFile(hash: String) extends FState
  type State = Map[Path, FState]

  def isDir(st: State, p: Path): Boolean = st.get(p) == Some(FDir)

  def doesNotExist(st: State, p: Path): Boolean = !st.contains(p)

  def isFile(st: State, p: Path): Boolean = st.get(p) match {
    case Some(FFile(_)) => true
    case _ => false
  }

  def isEmptyDir(st: State, p: Path) = {
    !st.toSeq.exists({ case (p1, s) => p1.startsWith(p) && p1 != p })
  }

  def evalPred(st: State, pred: Pred): Boolean = pred match {
    case True => true
    case False => false
    case ITE(a, b, c) => {
      if (evalPred(st, a)) {
        evalPred(st, b)
      }
      else {
        evalPred(st, c)
      }
    }
    case And(a, b) => evalPred(st, a) && evalPred(st, b)
    case Or(a, b) =>  evalPred(st, a) || evalPred(st, b)
    case Not(a) => !evalPred(st ,a)
    case TestFileState(p, IsFile) => isFile(st, p)
    case TestFileState(p, IsDir) => isDir(st, p)
    case TestFileState(p, DoesNotExist) => doesNotExist(st, p)
  }

  def eval(st: State, expr: Expr): S = expr match {
    case Error => None
    case Skip => Some(st)
    case Mkdir(p) => {
      if (doesNotExist(st, p) && isDir(st, p.getParent)) {
        Some(st + (p -> FDir))
      }
      else {
        None
      }
    }
    case CreateFile(p, h) => {
      if (isDir(st, p.getParent) && doesNotExist(st, p)) {
        Some(st + (p -> FFile(h)))
      }
      else {
        None
      }
    }
    case Cp(src, dst) => throw NotImplemented("not implemented")
    case Rm(p) => {
      if (isFile(st, p) || isEmptyDir(st, p)) {
        Some(st - p)
      }
      else {
        None
      }
    }
    case Seq(e1, e2) => eval(st, e1).flatMap(st_ => eval(st_, e2))
    case If(pred, e1, e2) => {
      if (evalPred(st, pred)) {
        eval(st, e1)
      }
      else {
        eval(st, e2)
      }
    }
  }

  def evalErr(s: S, expr: Expr): S = s match {
    case None => None
    case Some(st) => eval(st, expr)
  }

}
