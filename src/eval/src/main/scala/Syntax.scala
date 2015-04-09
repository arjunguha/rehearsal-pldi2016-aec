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

  lazy val readSet = Commutativity.predReadSet(this)
}

case object True extends Pred
case object False extends Pred
case class And(a: Pred, b: Pred) extends Pred
case class Or(a: Pred, b: Pred) extends Pred
case class Not(a: Pred) extends Pred
case class TestFileState(path: Path, s: FileState) extends Pred

object Pred {

  def implies(a: Pred, b: Pred): Pred = Or(Not(a), b)

}


sealed abstract trait Expr extends Product {
  def pretty(): String = Pretty.pretty(Pretty.AltCxt, this)
  def commutesWith(other: Expr) = Commutativity.commutes(this, other)

  def size(): Int
  lazy val readSet = Commutativity.exprReadSet(this)

  lazy val writeSet = Commutativity.exprWriteSet(this)
  
  lazy val idemSet = Commutativity.exprIdemSet(this)

  override lazy val hashCode: Int =
    runtime.ScalaRunTime._hashCode(this)

  override def toString(): String = this.pretty()

  // True if there are no concurrent expressions nested within this expression.
  val isSequential: Boolean
}

case object Error extends Expr {
  val size = 1
  val isSequential = true
}
case object Skip extends Expr {
  val size = 1
  val isSequential = true
}
case class Filter(a: Pred) extends Expr {
  val size = 1
  val isSequential = true
}
case class If(a: Pred, p: Expr, q: Expr) extends Expr {
  def size() = p.size + q.size
  val isSequential = p.isSequential && q.isSequential
}
case class Seq(p: Expr, q: Expr) extends Expr {
  def size() = p.size + q.size
  val isSequential = p.isSequential && q.isSequential
}

case class Alt(p: Expr, q: Expr) extends Expr {
  def size() = p.size + q.size
  val isSequential = p.isSequential && q.isSequential
}

case class Atomic(p: Expr) extends Expr {
  def size() = p.size + 1
  val isSequential = p.isSequential
}

case class Concur(p: Expr, q: Expr) extends Expr {
  def size() = p.size + q.size
  val isSequential = false

  lazy val commutes: Boolean = {
    (p.writeSet intersect q.writeSet).isEmpty &&
    (p.readSet intersect q.writeSet).isEmpty &&
    (p.writeSet intersect q.readSet).isEmpty &&
    /* its ok to have same paths in idemSets for p and q
     * but any path in p expr's idemSet should not occur
     * in read and write set of q expr and vice versa.
     */
    (p.idemSet intersect q.readSet).isEmpty &&
    (p.idemSet intersect q.writeSet).isEmpty &&
    (p.readSet intersect q.idemSet).isEmpty &&
    (p.writeSet intersect q.idemSet).isEmpty
  }
}

case class Mkdir(path: Path) extends Expr {
  val size = 1
  val isSequential = true
}

case class CreateFile(path: Path, hash: Array[Byte]) extends Expr {
  require(hash.length == 16,
          s"hashcode must be 16 bytes long (got ${hash.length})")
  val size = 1
  val isSequential = true
}

case class Rm(path: Path) extends Expr {
  val size = 1
  val isSequential = true
}

case class Cp(src: Path, dst: Path) extends Expr {
  val size = 1
  val isSequential = true
}
