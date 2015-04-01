package eval

import java.nio.file.Path

sealed trait FileState
case object IsFile extends FileState
case object IsDir extends FileState
case object DoesNotExist extends FileState

sealed trait Pred {
  def &&(other: Pred): Pred = And(this, other)
  def ||(other: Pred): Pred = Or(this, other)
  def unary_!(): Pred = Not(this)

  def readSet(): Stream[Path]
  def writeSet(): Stream[Path] = Stream()
}

case object True extends Pred {
  lazy val readSet = Stream[Path]()
}
case object False extends Pred {
  lazy val readSet = Stream[Path]()
}
case class And(a: Pred, b: Pred) extends Pred {
  lazy val readSet = a.readSet union b.readSet
}
case class Or(a: Pred, b: Pred) extends Pred {
  lazy val readSet = a.readSet union b.readSet
}
case class Not(a: Pred) extends Pred {
  lazy val readSet = a.readSet
}
case class TestFileState(path: Path, s: FileState) extends Pred {
  lazy val readSet = Stream(path)
}

object Pred {

  def implies(a: Pred, b: Pred): Pred = Or(Not(a), b)

}


sealed abstract trait Expr extends Product {
  def pretty(): String = Pretty.pretty(Pretty.AltCxt, this)
  def commutesWith(other: Expr) = Commutativity.commutes(this, other)

  def size(): Int
  def readSet(): Stream[Path]
  def writeSet(): Stream[Path]

  override lazy val hashCode: Int =
    runtime.ScalaRunTime._hashCode(this)

  override def toString(): String = this.pretty()
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
