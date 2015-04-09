package eval

import java.nio.file.Path

private[eval] object Commutativity {

  def predReadSet(pred: Pred): Set[Path] = {
    pred match {
      case True | False => Set()
      case And(a, b) => predReadSet(a) ++ predReadSet(b)
      case Or(a, b) => predReadSet(a) ++ predReadSet(b)
      case Not(a) => predReadSet(a)
      case TestFileState(path, _) => Set(path)
    }
  }

  def exprReadSet(expr: Expr): Set[Path] = expr match {
    case If(TestFileState(d1, IsDir), Skip, Mkdir(d2)) => {
      if (d1 == d2) { Set() }
      else { Set(d1) }
    }
    case If(TestFileState(d1, DoesNotExist), Mkdir(d2), Skip) => {
      if (d1 == d2) { Set() }
      else { Set(d1) }
    }
    case Error => Set()
    case Skip => Set()
    case Filter(a) => predReadSet(a)
    case If(a, p, q) => predReadSet(a) ++ exprReadSet(p) ++ exprReadSet(q)
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
    case If(TestFileState(d1, IsDir), Skip, Mkdir(d2)) => {
      if (d1 == d2) { Set() }
      else { Set(d2) }
    }
    case If(TestFileState(d1, DoesNotExist), Mkdir(d2), Skip) => {
      if (d1 == d2) { Set() }
      else { Set(d2) }
    }
    case Error => Set()
    case Skip => Set()
    case Filter(_) => Set()
    case If(a, p, q) => exprWriteSet(p) ++ exprWriteSet(q)
    case Concur(p, q) => exprWriteSet(p) ++ exprWriteSet(q)
    case Seq(p, q) => exprWriteSet(p) ++ exprWriteSet(q)
    case Alt(p, q) => exprWriteSet(p) ++ exprWriteSet(q)
    case Atomic(p) => exprWriteSet(p)
    case Mkdir(path) => Set(path)
    case CreateFile(path, _) => Set(path)
    case Rm(path) => Set(path)
    case Cp(_, dst) => Set(dst)
  }

  def isIdempotent(expr: Expr) = expr match {
    case If(TestFileState(d1, IsDir), Skip, Mkdir(d2)) => true
    case _ => false
  }

  def exprIdemSet(expr: Expr): Set[Path] =
    if(isIdempotent(expr)) expr.readSet union expr.writeSet
    else Set()

  def commutes(p: Expr, q: Expr): Boolean = {

    val pr = exprReadSet(p)
    val pw = exprWriteSet(p)
    val qr = exprReadSet(q)
    val qw = exprWriteSet(q)
    val pi = exprIdemSet(p)
    val qi = exprIdemSet(q)

    // no write-write conflicts
    (pw intersect qw).isEmpty &&
    // no read-write conflicts
    (pr intersect qw).isEmpty && (pw intersect qr).isEmpty &&
    // no conflicts with idempotent operations
    (pi intersect qr).isEmpty && (pi intersect qw).isEmpty &&
    (pr intersect qi).isEmpty && (pw intersect qi).isEmpty
  }
}
