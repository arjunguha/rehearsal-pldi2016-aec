package rehearsal

object FSSyntax {

  import java.nio.file.Path
  import scalax.collection.Graph
  import scalax.collection.GraphEdge.DiEdge

  sealed trait FileState extends Ordered[FileState] {


    def compare(that: FileState): Int = {
      def toInt(x: FileState): Int = x match {
        case IsFile => 0
        case IsDir => 1
        case DoesNotExist => 2
      }
      toInt(this).compare(toInt(that))
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

    def &&(b: Pred): Pred = (this, b) match {
      case (True, _) => b
      case (_, True) => this
      case _ => And(this, b)
    }

    def ||(b: Pred): Pred = (this, b) match {
      case (True, _) => True
      case (False, _) => b
      case (_, True) => True
      case (_, False) => this
      case _ => Or(this, b)
    }

    def unary_!(): Pred = this match {
      case Not(True) => False
      case Not(False) => True
      case Not(a) => a
      case _ => Not(this)
    }

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

    val size = Helpers.size(this)
    val paths = Helpers.exprPaths(this)
    val hashes = Helpers.exprHashes(this)
    val (readSet, writeSet, idemSet) = Commutativity.exprFileSets(this)

    override lazy val hashCode: Int =
      runtime.ScalaRunTime._hashCode(this)

    override def toString(): String = this.pretty()


    def >>(e2: Expr) = (this, e2) match {
      case (Skip, _) => e2
      case (_, Skip) => this
      case (Error, _) => Error
      case (_, Error) => Error
      case _ => Seq(this, e2)
    }

    def eval(st: FSEvaluator.State): Option[FSEvaluator.State] = FSEvaluator.eval(st, this)

  }

  case object Error extends Expr
  case object Skip extends Expr
  case class If(a: Pred, p: Expr, q: Expr) extends Expr
  case class Seq(p: Expr, q: Expr) extends Expr
  case class Mkdir(path: Path) extends Expr
  case class CreateFile(path: Path, contents: String) extends Expr
  case class Rm(path: Path) extends Expr
  case class Cp(src: Path, dst: Path) extends Expr

  object Block {
    import Implicits._
    def apply(es: Expr*): Expr = es.foldRight(Skip: Expr)((e, expr) => e >> expr)
  }

  object And {
    def apply(preds: Pred*): Pred = preds.foldRight[Pred](True) { (x, y) => And(x, y) }
  }

}