package fsmodel

import java.nio.file.Path

sealed trait FileState
case object IsFile extends FileState
case object IsDir extends FileState
case object DoesNotExist extends FileState

sealed trait Pred {
  def &&(other: Pred): Pred = And(this, other)
  def ||(other: Pred): Pred = Or(this, other)
  def unary_!(): Pred = Not(this)
}

case object True extends Pred
case object False extends Pred
case class And(a: Pred, b: Pred) extends Pred
case class Or(a: Pred, b: Pred) extends Pred
case class Not(a: Pred) extends Pred
case class TestFileState(path: Path, s: FileState) extends Pred

sealed trait Expr {

  def collectPaths(): Set[Path] = CollectPaths.expr(this)

}

case object Error extends Expr
case object Skip extends Expr
case class Block(p: Expr, q: Expr) extends Expr // p; q
case class Alt(p: Expr, q: Expr) extends Expr // p + q
case class If(a: Pred, p: Expr, q: Expr) extends Expr
case class Mkdir(path: Path) extends Expr
case class CreateFile(path: Path, hash: Array[Byte]) extends Expr {
  require(hash.length == 16,
          s"hashcode must be 16 bytes long (got ${hash.length})")
}
case class Rm(path: Path) extends Expr
case class Cp(src: Path, dst: Path) extends Expr
case class Mv(src: Path, dst: Path) extends Expr

object CreateFile {
  private val zeroes = Array.fill[Byte](16)(0)

  def apply(path: Path): Expr = CreateFile(path, zeroes)
}

object Block {

  def apply(ps: Expr*): Expr = ps match {
    case Seq() => Skip
    case Seq(p, rest @ _ *) => Block(p, apply(rest : _ *))
  }

}

object Pred {

  def implies(a: Pred, b: Pred): Pred = Or(Not(a), b)

}

object CollectPaths {

  def pred(a: Pred): Set[Path] = a match {
    case True => Set()
    case False => Set()
    case And(a, b) => pred(a) ++ pred(b)
    case Or(a, b) => pred(a) ++ pred(b)
    case Not(a) => pred(a)
    case TestFileState(p, _) => Set(p)
  }

  def expr(e: Expr): Set[Path] = e match {
    case Error => Set()
    case Skip => Set()
    case Block(e1, e2) => expr(e1) ++ expr(e2)
    case Alt(e1, e2) => expr(e1) ++ expr(e2)
    case If(a, e1, e2) => pred(a) ++ expr(e1) ++ expr(e2)
    case Mkdir(p) => Set(p)
    case CreateFile(p, _) => Set(p)
    case Rm(p) => Set(p)
    case Cp(p1, p2) => Set(p1, p2)
    case Mv(p1, p2) => Set(p1, p2)
  }

}