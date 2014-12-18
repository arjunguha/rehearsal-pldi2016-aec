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

sealed trait Expr
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