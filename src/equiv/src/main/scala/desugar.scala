package equiv.desugar

import equiv.ast._
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


object Desugar {

  private val id: ExprC = App(True)

  def apply (expr: Expr): ExprC = expr match {
    case Block(exprs @ _*) if 0 == exprs.size => id
    case Block(exprs @ _*) if 1 == exprs.size => Desugar(exprs(0))
    case Block(exprs @ _*) => exprs.foldRight(id)((e, acc) => Seq(Desugar(e), acc))
    case If(cond, trueBranch, falseBranch) => Union(Seq(App(cond), Desugar(trueBranch)),
                                                    Seq(App(Not(cond)), Desugar(falseBranch)))
    case CreateFile(p, c) => CreateFileC(p, c)
    case DeleteFile(p) => DeleteFileC(p)
    case MkDir(p) => MkDirC(p)
    case RmDir(p) => RmDirC(p)
    case Link(p, t) => LinkC(p, t)
    case Unlink(p) => UnlinkC(p)
    case ShellExec(cmd) => ShellExecC(cmd)
  }
}
