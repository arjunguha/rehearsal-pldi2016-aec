package eval

import java.nio.file.Path

sealed trait FileState
case object IsFile extends FileState
case object IsDir extends FileState
case object DoesNotExist extends FileState

sealed trait Pred {
  lazy val readSet = Commutativity.predReadSet(this)
}

case object True extends Pred
case object False extends Pred
case class And(a: Pred, b: Pred) extends Pred
case class Or(a: Pred, b: Pred) extends Pred
case class Not(a: Pred) extends Pred
case class TestFileState(path: Path, s: FileState) extends Pred

sealed abstract trait Expr extends Product {
  def pretty(): String = Pretty.pretty(Pretty.AltCxt, this)
  def commutesWith(other: Expr) = Commutativity.commutes(this, other)

  val size = Helpers.size(this)
  val isSequential = Helpers.isSequential(this)

  val (readSet, writeSet, idemSet) = Commutativity.exprFileSets(this)

  override lazy val hashCode: Int =
    runtime.ScalaRunTime._hashCode(this)

  override def toString(): String = this.pretty()
}

case object Error extends Expr
case object Skip extends Expr
case class If(a: Pred, p: Expr, q: Expr) extends Expr
case class Seq(p: Expr, q: Expr) extends Expr
case class Alt(p: Expr, q: Expr) extends Expr
case class Atomic(p: Expr) extends Expr
case class Concur(p: Expr, q: Expr) extends Expr {
  lazy val commutes = p.commutesWith(q)
}
case class Mkdir(path: Path) extends Expr
case class CreateFile(path: Path, hash: Array[Byte]) extends Expr {
  require(hash.length == 16,
          s"hashcode must be 16 bytes long (got ${hash.length})")
}
case class Rm(path: Path) extends Expr
case class Cp(src: Path, dst: Path) extends Expr