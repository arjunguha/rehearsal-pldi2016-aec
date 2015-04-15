package eval

object Helpers {

  // True if there are no concurrent expressions nested within this expression.
  private[eval] def isSequential(expr: Expr): Boolean = expr match {
    case Error => true
    case Skip => true
    case Filter(_) => true
    case If(_, p, q) => p.isSequential && q.isSequential
    case Seq(p, q) => p.isSequential && q.isSequential
    case Alt(p, q) => p.isSequential && q.isSequential
    case Atomic(p) => p.isSequential
    case Concur(_, _) => false
    case Mkdir(_) => true
    case CreateFile(_, _) => true
    case Rm(_) => true
    case Cp(_, _) => true
  }

  // Gives all predicates size 0
  private[eval] def size(expr: Expr): Int = expr match {
    case Error => 1
    case Skip => 1
    case Filter(_) => 1
    case If(_, p, q) => 1 + p.size + q.size
    case Seq(p, q) => 1 + p.size + q.size
    case Alt(p, q) => 1 + p.size + q.size
    case Atomic(p) => 1 + p.size
    case Concur(p, q) => 1 + p.size + q.size
    case Mkdir(_) => 1
    case CreateFile(_, _) => 1
    case Rm(_) => 1
    case Cp(_, _) => 1
  }

}