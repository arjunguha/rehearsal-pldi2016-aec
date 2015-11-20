package rehearsal

object FSSyntax {

  import java.nio.file.Path
  import scalax.collection.Graph
  import scalax.collection.GraphEdge.DiEdge



  case class FileSets(reads: Set[Path], writes: Set[Path], dirs: Set[Path]) {
    require((reads intersect dirs).isEmpty, "read-set overlaps with dir-set")
    require((writes intersect dirs).isEmpty, "write-set overlaps with dir-set")

    def commutes(other: FileSets): Boolean = {
      val w = this.writes intersect other.writes
      val rw = this.reads intersect other.writes
      val wr = this.writes intersect other.reads
      rw.isEmpty &&
      wr.isEmpty &&
      w.isEmpty &&
      (this.dirs intersect other.reads).isEmpty &&
      (this.dirs intersect other.writes).isEmpty &&
      (other.dirs intersect this.reads).isEmpty &&
      (other.dirs intersect this.writes).isEmpty
    }

    /*
     * Take in approx file sets and return exact files sets
     *
     * If there is an overlap between read-write and idempotent
     * set of an expr, then the idempotent op on the intersecting
     * path is not idempotent
     */
    def combine(other: FileSets): FileSets = {
      val reads = this.reads ++ other.reads
      val writes = this.writes ++ other.writes
      val dirs = this.dirs ++ other.dirs
      val notDirs = dirs intersect (reads ++ writes)
      FileSets(reads ++ notDirs, writes ++ notDirs, dirs -- notDirs)
    }

    def withReads(newReads: Set[Path]): FileSets = {
      this.combine(FileSets(newReads, Set(), Set()))
    }

  }

  sealed trait FileState extends Ordered[FileState] {

    def compare(that: FileState): Int = {
      def toInt(x: FileState): Int = x match {
        case IsFile => 0
        case IsDir => 1
        case DoesNotExist => 2
      }
      val x = toInt(this).compare(toInt(that))
      if (x > 0) 1 else if (x < 0) -1 else 0
    }

  }

  case object IsFile extends FileState
  case object IsDir extends FileState
  case object DoesNotExist extends FileState

  sealed trait Pred {
    def size = Helpers.predSize(this)
    override def toString(): String = Pretty.prettyPred(Pretty.NotCxt, this)

    lazy val readSet = Commutativity.predReadSet(this)

    def &&(b: Pred): Pred = (this, b) match {
      case (True, _) => b
      case (_, True) => this
      case _ => internPred(And(this, b))
    }

    def ||(b: Pred): Pred = (this, b) match {
      case (True, _) => True
      case (False, _) => b
      case (_, True) => True
      case (_, False) => this
      case _ => internPred(Or(this, b))
    }

    def unary_!(): Pred = this match {
      case Not(True) => False
      case Not(False) => True
      case Not(a) => a
      case _ => internPred(Not(this))
    }

  }

  case object True extends Pred
  case object False extends Pred
  case class And private[FSSyntax](a: Pred, b: Pred) extends Pred
  case class Or private[FSSyntax](a: Pred, b: Pred) extends Pred
  case class Not private[FSSyntax](a: Pred) extends Pred
  case class TestFileState private[FSSyntax](path: Path, s: FileState) extends Pred {
    def <(tfs: TestFileState): Boolean = (this, tfs) match {
      case (TestFileState(f, x), TestFileState(g, y)) => if (f.toString == g.toString) {
        x < y
      } else {
        f.toString < g.toString
      }
    }
  }

  sealed abstract trait Expr {
    def pretty(): String = Pretty.pretty(this)
    def commutesWith(other: Expr) = this.fileSets.commutes(other.fileSets)

    lazy val size = Helpers.size(this)
    lazy val paths = Helpers.exprPaths(this)
    lazy val hashes = Helpers.exprHashes(this)

    lazy val fileSets = Commutativity.exprFileSets(this)
    lazy val isEffectFree = Helpers.isEffectFree(this)

    override def toString(): String = this.pretty()

    def >>(e2: Expr) = (this, e2) match {
      case (Skip, _) => e2
      case (_, Skip) => this
      case (Error, _) => Error
      case (_, Error) => Error
      case (If (a, Skip, Error), If (b, Skip, Error)) => ite(a && b, Skip, Error)
      case _ => seq(this, e2)
    }

    def eval(st: FSEvaluator.State): Option[FSEvaluator.State] = FSEvaluator.eval(st, this)

    def pruneIdem(): Expr = IdempotenceOptimizer.prune(this)

    def isIdempotent(): Boolean = {
      val impl = new SymbolicEvaluatorImpl(this.paths.toList, this.hashes, Set(), None)
      val r = impl.isIdempotent(this)
      impl.smt.free()
      r
    }

  }

  case object Error extends Expr
  case object Skip extends Expr
  case class If private[FSSyntax] (a: Pred, p: Expr, q: Expr) extends Expr
  case class Seq private[FSSyntax] (p: Expr, q: Expr) extends Expr
  case class Mkdir private[FSSyntax] (path: Path) extends Expr
  case class CreateFile private[FSSyntax] (path: Path, contents: String) extends Expr
  case class Rm private[FSSyntax] (path: Path) extends Expr
  case class Cp private[FSSyntax] (src: Path, dst: Path) extends Expr

  private val exprCache = scala.collection.mutable.HashMap[Expr, Expr]()

  private val predCache = scala.collection.mutable.HashMap[Pred, Pred]()

  private def internPred(a: Pred) = predCache.getOrElseUpdate(a, a)

  private def intern(e: Expr): Expr = exprCache.getOrElseUpdate(e, e)

  def ite(a: Pred, p: Expr, q: Expr): Expr = {
    if (p eq q) p else intern(If(a, p, q))
  }

  def seq(p: Expr, q: Expr) = intern(Seq(p, q))

  def mkdir(p: Path) = intern(Mkdir(p))

  def createFile(p: Path, c: String) = intern(CreateFile(p, c))

  def rm(p: Path) = intern(Rm(p))

  def cp(src: Path, dst: Path) = intern(Cp(src, dst))

  def testFileState(p: Path, s: FileState): TestFileState = internPred(TestFileState(p, s)).asInstanceOf[TestFileState]

  def clearCache(): Unit = {
    exprCache.clear()
  }

  object Block {
    import Implicits._
    def apply(es: Expr*): Expr = es.foldRight(Skip: Expr)((e, expr) => e >> expr)
  }

  object And {
    def apply(preds: Pred*): Pred = preds.foldRight[Pred](True) { (x, y) => And(x, y) }
  }

}
