package eval

private[eval] object Helpers {

  // True if there are no concurrent expressions nested within this expression.
  def isSequential(expr: Expr): Boolean = expr match {
    case Error => true
    case Skip => true
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
  def size(expr: Expr): Int = expr match {
    case Error => 1
    case Skip => 1
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

  // Converts predicates to negation normal form
  def nnf(pred: Pred): Pred = pred match {
    case Not(And(a, b)) => Or(nnf(Not(a)), nnf(Not(b)))
    case Not(Or(a, b)) => And(nnf(Not(a)), nnf(Not(b)))
    case Not(Not(a)) => nnf(a)
    case And(a, b) => And(nnf(a), nnf(b))
    case Or(a, b) => Or(nnf(a), nnf(b))
    case Not(a) => Not(nnf(a))
    case _ => pred
  }

  // Converts predicates from negation normal form to conjunctive normal form
  def cnf_from_nnf(pred: Pred): Pred = pred match {
    case Or(a, And(b, c)) => cnf_from_nnf(And(Or(a, b), Or(a, c)))
    case Or(And(b, c), a) => cnf_from_nnf(And(Or(b, a), Or(c, a)))
    case And(a, b) => And(cnf_from_nnf(a), cnf_from_nnf(b))
    case Or(a, b) => Or(cnf_from_nnf(a), cnf_from_nnf(b))
    case Not(a) => Not(cnf_from_nnf(a))
    case _ => pred
  }

  // Converts predicates to conjunctive normal form
  def cnf(pred: Pred): Pred = cnf_from_nnf(nnf(pred))

  // Replaces a with b in pred.
  def replace(pred: Pred, a: Pred, b: Pred): Pred = pred match {
    case x if (a == x) => b
    case Or(x, y) => Or(replace(x, a, b), replace(y, a, b))
    case And(x, y) => And(replace(x, a, b), replace(y, a, b))
    case Not(x) => Not(replace(x, a, b))
    case _ => pred
  }
}
