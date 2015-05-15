package rehearsal.fsmodel

import java.nio.file.Path
import Implicits._

private[fsmodel] object Helpers {

  def predSize(pred: Pred): Int = pred match {
    case Not(a) => 1 + a.size
    case And(a, b) => 1 + a.size + b.size
    case Or(a, b) => 1 + a.size + b.size
    case TestFileState(_, _) => 1
    case True => 1
    case False => 1
    case ITE(a, b, c) => 1 + a.size + b.size + c.size
  }

  def size(expr: Expr): Int = expr match {
    case Error => 1
    case Skip => 1
    case If(a, p, q) => 1 + a.size + p.size + q.size
    case Seq(p, q) => 1 + p.size + q.size
    case Mkdir(_) => 1
    case CreateFile(_, _) => 1
    case Rm(_) => 1
    case Cp(_, _) => 1
  }

  def nnf(pred: Pred): Pred = pred match {
    case Not(And(a, b)) => Or(nnf(Not(a)), nnf(Not(b)))
    case Not(Or(a, b)) => And(nnf(Not(a)), nnf(Not(b)))
    case Not(Not(a)) => nnf(a)
    case And(a, b) => And(nnf(a), nnf(b))
    case Or(a, b) => Or(nnf(a), nnf(b))
    case Not(a) => Not(nnf(a))
    case _ => pred
  }

  def cnf(pred: Pred): Pred = {
    def cnfFromNnf(pred: Pred): Pred = pred match {
      case Or(a, And(b, c)) => cnfFromNnf(And(Or(a, b), Or(a, c)))
      case Or(And(b, c), a) => cnfFromNnf(And(Or(b, a), Or(c, a)))
      case And(a, b) => And(cnfFromNnf(a), cnfFromNnf(b))
      case Or(a, b) => Or(cnfFromNnf(a), cnfFromNnf(b))
      case Not(a) => Not(cnfFromNnf(a))
      case _ => pred
    }
    cnfFromNnf(nnf(pred))
  }

  def replace(pred: Pred, a: Pred, b: Pred): Pred = pred match {
    case x if (a == x) => b
    case Or(x, y) => Or(replace(x, a, b), replace(y, a, b))
    case And(x, y) => And(replace(x, a, b), replace(y, a, b))
    case Not(x) => Not(replace(x, a, b))
    case _ => pred
  }

  def simplify(pred: Pred): Pred = pred match {
    case Or(True, _) => True
    case Or(_, True) => True
    case And(False, _) => False
    case And(_, False) => False
    case Or(False, p) => simplify(p)
    case Or(p, False) => simplify(p)
    case And(True, p) => simplify(p)
    case And(p, True) => simplify(p)
    case Not(p) => !simplify(p)
    case Or(Not(x), y) if (x == y) => True
    case Or(x, Not(y)) if (x == y) => True
    case And(Not(x), y) if (x == y) => False
    case And(x, Not(y)) if (x == y) => False
    case And(a, b) if (a == b) => simplify(a)
    case Or(a, b) if (a == b) => simplify(a)
    case And(a, b) => simplify(a) && simplify(b)
    case Or(a, b) => simplify(a) || simplify(b)
    case _ => pred
  }

  def ancestors(path: Path): Set[Path] = {
    if (path.getParent == null) {
      Set(path)
    }
    else {
      Set(path, path.getParent)
      // ancestors(path.getParent) + path
    }
  }

  def exprPaths(expr: Expr): Set[Path] = expr match {
    case Error => Set()
    case Skip => Set()
    case If(a, p, q) => a.readSet union exprPaths(p) union exprPaths(q)
    case Seq(p, q) => exprPaths(p) union exprPaths(q)
    case Mkdir(f) => ancestors(f)
    case CreateFile(f, _) => ancestors(f)
    case Rm(f) => ancestors(f)
    case Cp(src, dst) => ancestors(src) union ancestors(dst)
  }

}
