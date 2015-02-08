package fsmodel.ext

import fsmodel.core
import fsmodel.core.Pred
import java.nio.file.Path

sealed abstract trait Expr {

  def unconcur(): Expr = Compiler.unconcur(this)
  def unatomic(): Expr = Compiler.unatomic(this)
  def pretty(): String = Pretty.pretty(Pretty.AltCxt, this)
  def toCore(): core.Expr = Compiler.toCore(this)

}

case object Error extends Expr
case object Skip extends Expr
case class Filter(a: Pred) extends Expr
case class Seq(p: Expr, q: Expr) extends Expr
case class Alt(p: Expr, q: Expr) extends Expr
case class Atomic(p: Expr) extends Expr
case class Concur(p: Expr, q: Expr) extends Expr
case class Mkdir(path: Path) extends Expr
case class CreateFile(path: Path, hash: Array[Byte]) extends Expr {
  require(hash.length == 16,
          s"hashcode must be 16 bytes long (got ${hash.length})")
}
case class Rm(path: Path) extends Expr
case class Cp(src: Path, dst: Path) extends Expr
