package equiv.desugar

import equiv.ast
import equiv.ast._
import java.nio.file.{Path, Paths}

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
case class Filter(pred: ast.Predicate) extends FSKATExpr
case class Seqn(exprs: FSKATExpr*) extends FSKATExpr
case class Opt(lhs: FSKATExpr, rhs: FSKATExpr) extends FSKATExpr

object FSKATExpr {

  def gatherPaths(e: FSKATExpr): Set[Path] = e match {
    case Id | Err => Set()
    case MkDir(p) => Set(p)
    case RmDir(p) => Set(p)
    case Create(p) => Set(p)
    case Link(p)  => Set(p)
    case Unlink(p) => Set(p)
    case Delete(p) => Set(p)
    case Shell(p) => Set(p) // TODO(arjun): fishy
    case Filter(pr) => equiv.ast.Predicate.gatherPaths(pr)
    case Seqn(exprs @ _*) => exprs.map(gatherPaths).toSet.flatten
    case Opt(lhs, rhs) => gatherPaths(lhs) union gatherPaths(rhs)
   }

}


object Desugar {

  def apply (expr: Expr): FSKATExpr = expr match {
    case Block(exprs @ _*) => Seqn((exprs.map(Desugar(_))):_*)
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
