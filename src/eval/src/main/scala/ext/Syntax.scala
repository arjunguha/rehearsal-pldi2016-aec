package fsmodel.ext

import fsmodel.core
import fsmodel.core.Pred
import java.nio.file.Path

sealed abstract trait Expr extends Product {
  def unconcur(): Expr = SimpleUnconcur.unconcur(this)
  def unconcurOpt(): Expr = OptUnconcur.unconcur(this)
  def pretty(): String = Pretty.pretty(Pretty.AltCxt, this)
  def commutesWith(other: Expr) = Commutativity.commutes(this, other)

  def size(): Int
  def readSet(): Stream[Path]
  def writeSet(): Stream[Path]

  override lazy val hashCode: Int =
    runtime.ScalaRunTime._hashCode(this)
}

case object Error extends Expr {
  val size = 1
  lazy val readSet = Stream[Path]()
  lazy val writeSet = Stream[Path]()
}
case object Skip extends Expr {
  val size = 1
  lazy val readSet = Stream[Path]()
  lazy val writeSet = Stream[Path]()
}
case class Filter(a: Pred) extends Expr {
  val size = 1
  lazy val readSet = a.readSet
  lazy val writeSet = a.writeSet
}
case class If(a: Pred, p: Expr, q: Expr) extends Expr {
  def size() = p.size + q.size
  lazy val readSet = a.readSet union p.readSet union q.readSet
  lazy val writeSet = a.writeSet union p.writeSet union q.writeSet
}
case class Seq(p: Expr, q: Expr) extends Expr {
  def size() = p.size + q.size
  lazy val readSet = p.readSet union q.readSet
  lazy val writeSet = p.writeSet union q.writeSet
}

case class Alt(p: Expr, q: Expr) extends Expr {
  def size() = p.size + q.size
  lazy val readSet = p.readSet union q.readSet
  lazy val writeSet = p.writeSet union q.writeSet
}

case class Atomic(p: Expr) extends Expr {
  def size() = p.size + 1
  lazy val readSet = p.readSet
  lazy val writeSet = p.writeSet
}

case class Concur(p: Expr, q: Expr) extends Expr {
  def size() = p.size + q.size
  lazy val readSet = p.readSet union q.readSet
  lazy val writeSet = p.writeSet union q.writeSet

  lazy val commutes: Boolean = {
    (p.writeSet intersect q.writeSet).isEmpty &&
    (p.readSet intersect q.writeSet).isEmpty &&
    (p.writeSet intersect q.readSet).isEmpty
  }
}

case class Mkdir(path: Path) extends Expr {
  val size = 1
  lazy val readSet = Stream[Path]()
  lazy val writeSet = Stream(path)
}

case class CreateFile(path: Path, hash: Array[Byte]) extends Expr {
  require(hash.length == 16,
          s"hashcode must be 16 bytes long (got ${hash.length})")
  val size = 1
  lazy val readSet = Stream[Path]()
  lazy val writeSet = Stream(path)
}
case class Rm(path: Path) extends Expr {
  val size = 1
  lazy val readSet = Stream[Path]()
  lazy val writeSet = Stream(path)
}
case class Cp(src: Path, dst: Path) extends Expr {
  val size = 1
  lazy val readSet = Stream(src)
  lazy val writeSet = Stream(dst)
}
