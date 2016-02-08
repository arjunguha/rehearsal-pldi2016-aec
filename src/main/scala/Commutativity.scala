package rehearsal

object Commutativity {

  import java.nio.file.Path
  import Implicits._
  import FSSyntax._

  sealed trait V {

    def <(other: V) = (this, other) match {
      case (Bot, R) => true
      case (Bot, D) => true
      case (_, W) => true
      case _ => false
    }

    def join(other: V) = (this, other) match {
      case (Bot, y) => y
      case (x, Bot) => x
      case (_, W) => W
      case (W, _) => W
      case (R, D) => W
      case (D, R) => W
      case (D, D) => D
      case (R, R) => R
    }

  }

  case object Bot extends V
  case object R extends V
  case object W extends V
  case object D extends V

  // type St = Map[Path, V]

  case class St(map: Map[Path, V]) {

    def apply(p: Path): V = map.get(p) match {
      case None => Bot
      case Some(v) => v
    }

    def join(other: St): St = {
      new St(this.map.combine(other.map) {
        case (None, Some(x)) => Some(x)
        case (Some(x), None) => Some(x)
        case (Some(x), Some(y)) => Some(x.join(y))
        case (None, None) => throw Unexpected("should not happen")
      })
    }

    def +(kv: (Path, V)): St = {
      val (p, v) = kv

      val v_ = (this(p), v) match {
        case (D, R) => D
        case (D, D) => D
        case (R, D) => W
        case (R, R) => R
        case (Bot, v) => v
        case (_, Bot) => throw Unexpected("should not happen")
        case (W, _) => W
        case (_, W) => W

      }
      new St(map + (p -> v_))
    }

    def reads(): Set[Path] = map.keys.filter(p => this(p) == R).toSet

    def writes(): Set[Path] = map.keys.filter(p => this(p) == W).toSet

    def dirs(): Set[Path] = map.keys.filter(p => this(p) == D).toSet

    def commutesWith(st2: St) = {
      val st1 = this

    (st1.reads intersect st2.writes).isEmpty &&
      (st1.writes intersect st2.reads).isEmpty &&
      (st1.writes intersect st2.writes).isEmpty && // TODO(arjun): typo in paper
      (st1.dirs intersect (st2.reads union st2.writes)).isEmpty &&
      ((st1.reads union st1.writes) intersect st2.dirs).isEmpty

    }

  }

  object St {

    // TODO(arjun): This is assumed by resourceModel too. should centralize
    // this configuration
    val empty = new St(Map("/".toPath -> D, "/etc".toPath -> D, "/bin".toPath -> D, "/usr".toPath -> D))

  }

  def evalPred(st: St, pred: Pred): St = pred match {
    case True => st
    case False => st
    case And(a, b) => evalPred(st, a) join evalPred(st, b)
    case Or(a, b) =>  evalPred(st, a) join evalPred(st, b)
    case Not(a) => evalPred(st, a)
    case TestFileState(p, _) => st + (p -> R) // TOOD(arjun): confirm we don't need p.getParent here
  }

  def evalExpr(st: St, expr: Expr): St = expr match {
    case Error => st
    case Skip => st
    case If(TestFileState(dir, IsDir), Skip, Mkdir(d_)) if dir == d_ => {
      if (st(dir) < D && st(dir.getParent) == D) {
        st + (dir -> D)
      }
      else {
        st + (dir -> W)
      }
    }
    case If(pred, e1, e2) => {
      val st_ = evalPred(st, pred)
      evalExpr(st_, e1) join evalExpr(st_, e2)
    }
    case Seq(e1, e2) => evalExpr(evalExpr(st, e1), e2)
    // Assumes that p != "/"
    case Mkdir(p) => {
      if (st(p.getParent) == D) {
        st + (p -> W)
      }
      else {
        st + (p -> W) + (p.getParent -> R)
      }
    }
    case CreateFile(p, _) => {
      if (st(p.getParent) == D) {
        st + (p -> W)
      }
      else {
        st + (p -> W) + (p.getParent -> R)
      }
    }
    case Rm(p) => {
      if (st(p.getParent) == D) {
        st + (p -> W)
      }
      else {
        st + (p -> W) + (p.getParent -> R)
      }
    }

    case Cp(src, dst) => st + (src -> R) + (dst -> W) + (dst.getParent -> R)
  }

  def commutesWith(e1: Expr, e2: Expr): Boolean = {
    val st1 = evalExpr(St.empty, e1)
    val st2 = evalExpr(St.empty, e2)
    st1.commutesWith(st2)
  }

  def absState(e: Expr) = evalExpr(St.empty, e)

  def predReadSet(pred: Pred): Set[Path] = pred match {
    case True | False => Set()
    case And(a, b) => a.readSet ++ b.readSet
    case Or(a, b) => a.readSet ++ b.readSet
    case Not(a) => a.readSet
    case TestFileState(path, _) => Set(path)
  }

}
