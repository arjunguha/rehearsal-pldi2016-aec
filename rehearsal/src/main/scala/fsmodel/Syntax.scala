package rehearsal.fsmodel

import java.nio.file.Path

sealed trait FileState {
  def <(s: FileState): Boolean = (this, s) match {
    case (IsFile, IsDir) => true
    case (IsFile, DoesNotExist) => true
    case (IsDir, DoesNotExist) => true
    case _ => false
  }
}

case object IsFile extends FileState
case object IsDir extends FileState
case object DoesNotExist extends FileState

sealed trait Pred {
  def nnf(): Pred = Helpers.nnf(this)
  def cnf(): Pred = Helpers.cnf(this)
  def replace(a: Pred, b: Pred): Pred = Helpers.replace(this, a, b)
  def size = Helpers.predSize(this)
  override def toString(): String = Pretty.prettyPred(Pretty.NotCxt, this)

  lazy val readSet = Commutativity.predReadSet(this)
}

case object True extends Pred
case object False extends Pred
case class And(a: Pred, b: Pred) extends Pred
case class Or(a: Pred, b: Pred) extends Pred
case class Not(a: Pred) extends Pred
case class TestFileState(path: Path, s: FileState) extends Pred {
  def <(tfs: TestFileState): Boolean = (this, tfs) match {
    case (TestFileState(f, x), TestFileState(g, y)) => if (f.toString == g.toString) {
      x < y
    } else {
      f.toString < g.toString
    }
  }
}
case class ITE(a: Pred, b: Pred, c: Pred) extends Pred

sealed abstract trait Expr extends Product {
  def pretty(): String = Pretty.pretty(this)
  def commutesWith(other: Expr) = Commutativity.commutes(this, other)
  def wp(post: Pred): Pred = WeakestPreconditions.wp(this, post)

  val size = Helpers.size(this)

  val paths = Helpers.exprPaths(this)
  val (readSet, writeSet, idemSet) = Commutativity.exprFileSets(this)

  override lazy val hashCode: Int =
    runtime.ScalaRunTime._hashCode(this)

  override def toString(): String = this.pretty()
}

case object Error extends Expr
case object Skip extends Expr
case class If(a: Pred, p: Expr, q: Expr) extends Expr
case class Seq(p: Expr, q: Expr) extends Expr
case class Mkdir(path: Path) extends Expr
case class CreateFile(path: Path, hash: Array[Byte]) extends Expr {
  require(hash.length == 16,
          s"hashcode must be 16 bytes long (got ${hash.length})")
}
case class Rm(path: Path) extends Expr
case class Cp(src: Path, dst: Path) extends Expr

object Block {
  import Implicits._
  def apply(es: Expr*): Expr = es.foldRight(Skip: Expr)((e, expr) => e >> expr)
}

object And {
  def apply(preds: Pred*): Pred = preds.foldRight[Pred](True) { (x, y) => And(x, y) }
}

object HashHelper {

  def exprHashes(expr: Expr): Set[List[Byte]] = expr match{
    case Error => Set()
    case Skip => Set()
    case If(a, p, q) => exprHashes(p) union exprHashes(q)
    case Seq(p, q) => exprHashes(p) union exprHashes(q)
    case Mkdir(f) => Set()
    case CreateFile(f, h) => Set(h.toList)
    case Rm(f) => Set()
    case Cp(src, dst) => Set()
  }
}
