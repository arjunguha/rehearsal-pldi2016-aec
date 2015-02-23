package fsmodel.ext

import java.nio.file.Path
import fsmodel.core.Pred

private[ext] object Commutativity {

  def predReadSet(pred: Pred): Set[Path] = {
    import fsmodel.core._
    pred match {
      case True | False => Set()
      case And(a, b) => predReadSet(a) ++ predReadSet(b)
      case Or(a, b) => predReadSet(a) ++ predReadSet(b)
      case Not(a) => predReadSet(a)
      case TestFileState(path, _) => Set(path)
    }
  }

  def exprReadSet(expr: Expr): Set[Path] = expr match {
    case Error => Set()
    case Skip => Set()
    case Filter(a) => predReadSet(a)
    case Concur(p, q) => exprReadSet(p) ++ exprReadSet(q)
    case Seq(p, q) => exprReadSet(p) ++ exprReadSet(q)
    case Alt(p, q) => exprReadSet(p) ++ exprReadSet(q)
    case Atomic(p) => exprReadSet(p)
    case Mkdir(_) => Set()
    case CreateFile(_, _) => Set()
    case Rm(_) => Set()
    case Cp(src, _) => Set(src)
  }

  def exprWriteSet(expr: Expr): Set[Path] = expr match {
    case Error => Set()
    case Skip => Set()
    case Filter(_) => Set()
    case Concur(p, q) => exprWriteSet(p) ++ exprWriteSet(q)
    case Seq(p, q) => exprWriteSet(p) ++ exprWriteSet(q)
    case Alt(p, q) => exprWriteSet(p) ++ exprWriteSet(q)
    case Atomic(p) => exprWriteSet(p)
    case Mkdir(path) => Set(path)
    case CreateFile(path, _) => Set(path)
    case Rm(path) => Set(path)
    case Cp(_, dst) => Set(dst)
  }

  def commutes(p: Expr, q: Expr): Boolean = {
    val pr = exprReadSet(p)
    val pw = exprWriteSet(p)
    val qr = exprReadSet(q)
    val qw = exprWriteSet(q)

    // no write-write conflicts
    (pw intersect qw).isEmpty &&
    // no read-write conflicts
    (pr intersect qw).isEmpty && (pw intersect qr).isEmpty
  }

}
