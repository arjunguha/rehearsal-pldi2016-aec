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

  def withFileState(pred: Pred, f: Path, s: FileState): Pred = s match {
    case IsFile => pred.replace(TestFileState(f, IsFile), True)
                       .replace(TestFileState(f, IsDir), False)
                       .replace(TestFileState(f, DoesNotExist), False)
    case IsDir => pred.replace(TestFileState(f, IsDir), True)
                      .replace(TestFileState(f, IsFile), False)
                      .replace(TestFileState(f, DoesNotExist), False)
    case DoesNotExist => pred.replace(TestFileState(f, DoesNotExist), True)
                             .replace(TestFileState(f, IsDir), False)
                             .replace(TestFileState(f, IsFile), False)
  }

  // Calculates the weakest-precondition for an expression yielding the desired postcondition.
  def wp(expr: Expr, post: Pred): Pred = expr match {
    case Error => False
    case Skip => post
    case If(a, p, q) => (!a || wp(p, post)) && (a || wp(q, post))
    case Seq(p, q) => wp(p, wp(q, post))
    case Mkdir(f) => withFileState(post, f, IsDir) && (TestFileState(f, DoesNotExist) &&
                                                       TestFileState(f.getParent(), IsDir))
    case CreateFile(f, _) => withFileState(post, f, IsFile) && (TestFileState(f, DoesNotExist) &&
                                                                TestFileState(f.getParent(), IsDir))
    case Rm(f) => withFileState(post, f, DoesNotExist) && TestFileState(f, IsFile)
    case Cp(f, g) => post.replace(TestFileState(g, DoesNotExist), False)
      .replace(TestFileState(g, IsFile), TestFileState(f, IsFile))
      .replace(TestFileState(g, IsDir), TestFileState(f, IsDir)) &&
      (TestFileState(g, DoesNotExist) && !TestFileState(f, DoesNotExist))
    case _ => False
  }
}
