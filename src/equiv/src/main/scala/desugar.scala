package equiv.desugar

import equiv.ast._
import equiv.sat._
import z3.scala._
/*
import java.nio.file.Path

sealed trait ExprC

sealed trait OpC extends ExprC
case class CreateFileC(p: Path, c: Content) extends OpC
case class DeleteFileC(p: Path) extends OpC
case class MkDirC(p: Path) extends OpC
case class RmDirC(p: Path) extends OpC
case class LinkC(p: Path, t: Path) extends OpC
case class UnlinkC(p: Path) extends OpC
case class ShellExecC(cmd: String) extends OpC


case class App(pr: Predicate) extends ExprC
case class Seq(lhs: ExprC, rhs: ExprC) extends ExprC
case class Union(lhs: ExprC, rhs: ExprC) extends ExprC
*/


/*
object Desugar {

  private def desugarPredicate(pr: Predicate): Z3AST = pr match {
    case 

  def apply (expr: Expr)(implicit val z3: Z3Puppet): Z3AST = expr match {
    case Block(exprs @ _*) if 0 == exprs.size => Z3Puppet.id
    case Block(exprs @ _*) if 1 == exprs.size => Desugar(exprs(0))
    case Block(exprs @ _*) => exprs.foldRight(Z3Puppet.id)((e, acc) => Seq(Desugar(e), acc))
    case If(cond, trueBranch, falseBranch) => Z3Puppet.seq(App(cond), Desugar(trueBranch)),
                                                    Seq(App(Not(cond)), Desugar(falseBranch)))

    case CreateFile(p, _) => Z3Puppet.create(Z3Puppet.toZ3Path(p))
    case DeleteFile(p) => Z3Puppet.delete(Z3Puppet.toZ3Path(p))
    case MkDir(p) => Z3Puppet.mkdir(Z3Puppet.toZ3Path(p))
    case RmDir(p) => Z3Puppet.rmdir(Z3Puppet.toZ3Path(p))
    case Link(p, _) => Z3Puppet.link(Z3Puppet.toZ3Path(p))
    case Unlink(p) => Z3Puppet.unlink(Z3Puppet.toZ3Path(p))
    case ShellExec(cmd) => // Z3Puppet.shell(cmd)
  }
}
*/
