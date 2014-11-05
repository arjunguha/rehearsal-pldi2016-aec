package equiv.desugar

import equiv.ast
import equiv.ast._
import java.nio.file.{Path, Paths}

// Resuse predicate from ast
/*
sealed trait FSKATPred
case object True extends FSKATPred
case object False extends FSKATPred
case class Exists(path: Path) extends FSKATPred
case class IsDir(path: Path) extends FSKATPred
case class IsFile(path: Path) extends FSKATPred
case class IsLink(path: Path) extends FSKATPred
case class And(lhs: FSKATPred, rhs: FSKATPred) extends FSKATPred
case class Or(lhs: FSKATPred, rhs: FSKATPred) extends FSKATPred
case class Not(oper: FSKATPred) extends FSKATPred
*/


sealed trait FSKATExpr
case object Id extends FSKATExpr
case object Err extends FSKATExpr
case class MkDir(path: Path) extends FSKATExpr
case class RmDir(path: Path) extends FSKATExpr
case class Create(path: Path) extends FSKATExpr
case class Delete(path: Path) extends FSKATExpr
case class Link(path: Path) extends FSKATExpr
case class Unlink(path: Path) extends FSKATExpr
case class Shell(path: Path) extends FSKATExpr // TODO
case class Filter(pred: /*FSKATPred*/ ast.Predicate) extends FSKATExpr
case class Seqn(lhs: FSKATExpr, rhs: FSKATExpr) extends FSKATExpr
case class Opt(lhs: FSKATExpr, rhs: FSKATExpr) extends FSKATExpr


object Desugar {

  /*
  private def DesugarPred(pr: Predicate)(implicit z3: Z3Puppet): Z3AST = pr match {
    case True => 
    case False => z3.context.mkFalse
    case Exists(p) => z3.pexists(z3.toZ3Path(p))
    case IsDir(p) => z3.isdir(z3.toZ3Path(p))
    case IsLink(p) => z3.islink(z3.toZ3Path(p))
    case IsRegularFile(p) => z3.isregularfile(z3.toZ3Path(p))
    case ast.And(lhs, rhs) => (DesugarPred(lhs) && DesugarPred(rhs)).ast(z3.context)
    case ast.Or(lhs, rhs) => (DesugarPred(lhs) || DesugarPred(rhs)).ast(z3.context)
    case ast.Not(pr) => (!DesugarPred(pr)).ast(z3.context)
    case IsEqual(lhs, rhs) => DesugarPred(lhs) === DesugarPred(rhs)
  }
  */

  def apply (expr: Expr): FSKATExpr = expr match {
    case Block(exprs @ _*) if 0 == exprs.size => Id
    case Block(exprs @ _*) if 1 == exprs.size => Desugar(exprs(0))
    case Block(exprs @ _*) => exprs.foldRight(Id: FSKATExpr)((e, acc) => Seqn(Desugar(e), acc))
    case ast.Filter(a) => Filter(a)
    case If(cond, trueBranch, falseBranch) => Opt(Seqn(Filter(cond), Desugar(trueBranch)),
                                                  Seqn(Filter(ast.Not(cond)),  Desugar(falseBranch)))
    case CreateFile(p, _) => Create(p)
    case DeleteFile(p) => Delete(p)
    case ast.MkDir(p) => MkDir(p)
    case ast.RmDir(p) => RmDir(p)
    case ast.Link(p, _) => Link(p)
    case ast.Unlink(p) => Unlink(p)
    case ShellExec(cmd) => Shell(Paths.get("/tmp/script.sh")) // Assume that command is written to file /tmp/script.sh which shell executes
  }
}
