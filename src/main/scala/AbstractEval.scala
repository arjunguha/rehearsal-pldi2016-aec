package rehearsal

object AbstractEval {

  import java.nio.file.Path
  import FSSyntax._
  import Implicits._

  sealed trait Stat
  case object Dir extends Stat
  case object File extends Stat
  case object DoesNotExist extends Stat

  trait StateLike[A] {
    def >>(other: A): A
    def +(other: A): A
    def unary_!(): A
  }

  trait EvalLike {

    type State <: StateLike[State]

    def test(p: Path, stat: Stat): State
    def set(p: Path, stat: Stat): State
    def error: State
    def skip: State

    def evalPred(pred: Pred): State = pred match {
      case True => skip
      case False => error
      case And(a, b) => evalPred(a) >> evalPred(b)
      case Or(a, b) => evalPred(a) + evalPred(b)
      case Not(a) => !evalPred(a)
      case TestFileState(p, IsFile) => test(p, File)
      case TestFileState(p, IsDir) => test(p, Dir)
      case TestFileState(p, FSSyntax.DoesNotExist) => test(p, DoesNotExist)
    }

    def eval(expr: Expr): State = expr match {
      case Mkdir(p) => {
        test(p.getParent, Dir) >> test(p, DoesNotExist) >> set(p, Dir)
      }
      case CreateFile(p, _) => {
        test(p.getParent, Dir) >> test(p, DoesNotExist) >> set(p, File)
      }
      case Rm(p) => {
        test(p, File) >> set(p, DoesNotExist)
      }
      case Cp(src, dst) => {
        test(src, File) >> test(dst.getParent, Dir) >>
          test(dst, DoesNotExist) >> set(dst, File)
      }
      case Error => error
      case Skip => skip
      case If(pred, e1, e2) => {
        val s = evalPred(pred)
        (s >> eval(e1)) + (!s >> eval(e2))
      }
      case Seq(e1, e2) => eval(e1) >> eval(e2)
    }

  }

}
