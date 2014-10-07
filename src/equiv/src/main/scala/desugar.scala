package equiv.desugar

import equiv.ast
import equiv.ast._
import equiv.sat._
import z3.scala._
import z3.scala.dsl._

object Desugar {

  private def DesugarPred(pr: Predicate)(implicit z3: Z3Puppet): Z3AST = pr match {
    case True => (true).ast(z3.context)
    case False => (false).ast(z3.context)
    case Exists(p) => z3.pexists(z3.toZ3Path(p))
    case IsDir(p) => z3.isdir(z3.toZ3Path(p))
    case IsLink(p) => z3.islink(z3.toZ3Path(p))
    case IsRegularFile(p) => z3.isregularfile(z3.toZ3Path(p))
    case ast.And(lhs, rhs) => (DesugarPred(lhs) && DesugarPred(rhs)).ast(z3.context)
    case ast.Or(lhs, rhs) => (DesugarPred(lhs) && DesugarPred(rhs)).ast(z3.context)
    case ast.Not(pr) => (!DesugarPred(pr)).ast(z3.context)
    case IsEqual(lhs, rhs) => DesugarPred(lhs) === DesugarPred(rhs)
  }

  def apply (expr: Expr)(implicit z3: Z3Puppet): Z3AST = expr match {
    case Block(exprs @ _*) if 0 == exprs.size => z3.id()
    case Block(exprs @ _*) if 1 == exprs.size => Desugar(exprs(0))
    case Block(exprs @ _*) => exprs.foldRight(z3.id())((e, acc) => z3.seq(Desugar(e), acc))
    case If(cond, trueBranch, falseBranch) => z3.union(DesugarPred(cond), Desugar(trueBranch), Desugar(falseBranch))
    case CreateFile(p, _) => z3.create(z3.toZ3Path(p))
    case DeleteFile(p) => z3.delete(z3.toZ3Path(p))
    case MkDir(p) => z3.mkdir(z3.toZ3Path(p))
    case RmDir(p) => z3.rmdir(z3.toZ3Path(p))
    case Link(p, _) => z3.link(z3.toZ3Path(p))
    case Unlink(p) => z3.unlink(z3.toZ3Path(p))
    case ShellExec(cmd) => z3.shell(z3.toZ3Cmd(cmd))
  }
}
