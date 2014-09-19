package verification.master.ast

// Surface Verification Lanuguage AST nodes
import java.nio.file.Path


sealed trait Predicate
case object True extends Predicate
case object False extends Predicate
case class Exists(p: Path) extends Predicate
case class IsDir(p: Path) extends Predicate
case class IsLink(p: Path) extends Predicate
case class IsRegularFile(p: Path) extends Predicate
case class And(lhs: Predicate, rhs: Predicate) extends Predicate
case class Or(lhs: Predicate, rhs: Predicate) extends Predicate
case class Not(oper: Predicate) extends Predicate
case class IsEqual(lhs: Predicate, rhs: Predicate) extends Predicate

/* Abstract Content */
class Content(str: String) {}
object Content {
  def apply(str: String): Content = new Content(str)
}

sealed trait Expr

case class Block(expr: Expr*) extends Expr
case class If(cond: Predicate, trueBranch: Expr, falseBranch: Expr) extends Expr

sealed trait Op extends Expr
case class CreateFile(p: Path, Content: Content) extends Op
case class DeleteFile(p: Path) extends Op
case class MkDir(p: Path) extends Op
case class RmDir(p: Path) extends Op
case class Link(p: Path, t: Path) extends Op
case class Unlink(p: Path) extends Op
case class ShellExec(cmd: String) extends Op

object ExprWellFormed {

  def PredicateWellFormed(pr: Predicate): Boolean = pr match {
    case True | False | Exists(_) | IsDir(_) | IsLink(_) | IsRegularFile(_)  => true
    case And(pr1, pr2) => PredicateWellFormed(pr1) && PredicateWellFormed(pr2)
    case Or(pr1, pr2) => PredicateWellFormed(pr1) && PredicateWellFormed(pr2)
    case Not(pr) => PredicateWellFormed(pr)
    case IsEqual(pr1, pr2) => PredicateWellFormed(pr1) && PredicateWellFormed(pr2)
  }

  def apply(e: Expr): Boolean = e match {
    case Block(exprs @ _*) => exprs.foldLeft(true)((acc, e) => acc && ExprWellFormed(e))
    case If(cond, e1, e2) => PredicateWellFormed(cond) && ExprWellFormed(e1) && ExprWellFormed(e2)
    case CreateFile(_, _)  => true
    case DeleteFile(_) => true
    case MkDir(_) => true
    case RmDir(_) => true
    case Link(_, _) => true
    case Unlink(_) => true
    case ShellExec(_) => true
  }
}

object PrettyPrint {

  def printPath(p: Path): String = p.toAbsolutePath.toString

  def printPred(pr: Predicate): String = pr match {
    case True => "true"
    case False => "false"
    case Exists(p) => "exists(%s)".format(printPath(p))
    case IsDir(p) => "isdir(%s)".format(printPath(p))
    case IsLink(p) => "islink(%s)".format(printPath(p))
    case IsRegularFile(p) => "isregularfile(%s)".format(printPath(p))
    case And(lhs, rhs) => printPred(lhs) + " && " + printPred(rhs)
    case Or(lhs, rhs) => printPred(lhs) + " || " + printPred(rhs)
    case Not(oper) => "! " + printPred(oper)
    case IsEqual(lhs, rhs) => printPred(lhs) + " == " + printPred(rhs)
  }

  def apply(e: Expr): String = e match {
    case Block(exprs @ _*) => " { " + 
                              exprs.map((e) => PrettyPrint(e)).mkString("; ") +
                               " } " + "\n"
    case If(cond, e1, e2) => "if (" + printPred(cond) + ")" + PrettyPrint(e1) + " else " + PrettyPrint(e2)
    case CreateFile(p, c) => s"create(${printPath(p)}, c)"
    case DeleteFile(p) => s"delete(${printPath(p)})"
    case MkDir(p) => s"mkdir(${printPath(p)})"
    case RmDir(p) => s"rmdir(${printPath(p)})"
    case Link(p, t) => s"link(${printPath(p)}, ${printPath(t)})"
    case Unlink(p) => s"unlink(${printPath(p)})"
    case ShellExec(cmd) => s"exec($cmd)"
  }
}
