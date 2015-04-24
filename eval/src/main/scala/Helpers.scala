package eval

import java.nio.file.Path
import Implicits._

private[eval] object Helpers {

  // Gives all predicates size 0
  def size(expr: Expr): Int = expr match {
    case Error => 1
    case Skip => 1
    case If(_, p, q) => 1 + p.size + q.size
    case Seq(p, q) => 1 + p.size + q.size
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
  def cnfFromNnf(pred: Pred): Pred = pred match {
    case Or(a, And(b, c)) => cnfFromNnf(And(Or(a, b), Or(a, c)))
    case Or(And(b, c), a) => cnfFromNnf(And(Or(b, a), Or(c, a)))
    case And(a, b) => And(cnfFromNnf(a), cnfFromNnf(b))
    case Or(a, b) => Or(cnfFromNnf(a), cnfFromNnf(b))
    case Not(a) => Not(cnfFromNnf(a))
    case _ => pred
  }

  // Converts predicates to conjunctive normal form
  def cnf(pred: Pred): Pred = cnfFromNnf(nnf(pred))

  // Replaces a with b in pred.
  def replace(pred: Pred, a: Pred, b: Pred): Pred = pred match {
    case x if (a == x) => b
    case Or(x, y) => Or(replace(x, a, b), replace(y, a, b))
    case And(x, y) => And(replace(x, a, b), replace(y, a, b))
    case Not(x) => Not(replace(x, a, b))
    case _ => pred
  }

}
