package fsmodel.ext

import fsmodel.core
import fsmodel.core.Pred
import java.nio.file.Path

sealed abstract trait Expr {
  def unconcur(): Expr = SimpleUnconcur.unconcur(this)
  def unconcurOpt(): Expr = OptUnconcur.unconcur(this)
  def unatomic(): Expr = Unatomic.unatomic(this)
  def pretty(): String = Pretty.pretty(Pretty.AltCxt, this)
  def toCore(): core.Expr = ToCore.toCore(this)
  def commutesWith(other: Expr) = Commutativity.commutes(this, other)

  def size(): Int

}

case object Error extends Expr {
  val size = 1
}
case object Skip extends Expr {
  val size = 1
}
case class Filter(a: Pred) extends Expr {
  val size = 1
}
case class If(a: Pred, p: Expr, q: Expr) extends Expr {
  def size() = p.size + q.size
}
case class Seq(p: Expr, q: Expr) extends Expr {
  def size() = p.size + q.size
}

case class Alt(p: Expr, q: Expr) extends Expr {
  def size() = p.size + q.size
}

case class Atomic(p: Expr) extends Expr {
  def size() = p.size + 1
}

case class Concur(p: Expr, q: Expr) extends Expr {
  def size() = p.size + q.size
}

case class Mkdir(path: Path) extends Expr {
  val size = 1
}

case class CreateFile(path: Path, hash: Array[Byte]) extends Expr {
  require(hash.length == 16,
          s"hashcode must be 16 bytes long (got ${hash.length})")
  val size = 1

}
case class Rm(path: Path) extends Expr {
  val size = 1
}
case class Cp(src: Path, dst: Path) extends Expr {
  val size = 1
}
