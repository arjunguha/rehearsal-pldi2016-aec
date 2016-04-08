package rehearsal

object FSSyntax {

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
      case (PTrue, _) => b
      case (_, PTrue) => this
      case _ => internPred(PAnd(this, b))
    }

    def ||(b: Pred): Pred = (this, b) match {
      case (PTrue, _) => PTrue
      case (PFalse, _) => b
      case (_, PTrue) => PTrue
      case (_, PFalse) => this
      case _ => internPred(POr(this, b))
    }

    def unary_!(): Pred = this match {
      case PNot(PTrue) => PFalse
      case PNot(PFalse) => PTrue
      case PNot(a) => a
      case _ => internPred(PNot(this))
    }

  }

  case object PTrue extends Pred
  case object PFalse extends Pred
  case class PAnd private[FSSyntax](a: Pred, b: Pred) extends Pred
  case class POr private[FSSyntax](a: Pred, b: Pred) extends Pred
  case class PNot private[FSSyntax](a: Pred) extends Pred
  case class PTestFileState private[FSSyntax](path: Path, s: FileState) extends Pred {
    def <(tfs: PTestFileState): Boolean = (this, tfs) match {
      case (PTestFileState(f, x), PTestFileState(g, y)) => if (f.toString == g.toString) {
        x < y
      } else {
        f.toString < g.toString
      }
    }
  }

  sealed abstract trait Expr {
    def pretty(): String = Pretty.pretty(this)
    def commutesWith(other: Expr) = this.fileSets.commutesWith(other.fileSets)

    lazy val size = Helpers.size(this)
    lazy val paths = Helpers.exprPaths(this)
    lazy val hashes = Helpers.exprHashes(this)

    lazy val fileSets = Commutativity.absState(this)

    override def toString(): String = this.pretty()

    def >>(e2: Expr) = (this, e2) match {
      case (ESkip, _) => e2
      case (_, ESkip) => this
      case (EError, _) => EError
      case (_, EError) => EError
      case (EIf (a, ESkip, EError), EIf (b, ESkip, EError)) => ite(a && b, ESkip, EError)
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

    /** Flattens a nested sequence. */
    def flatten(): Seq[Expr] = this match {
      case ESeq(head, tail) => head.flatten() ++ tail.flatten()
      case other => Seq(other)
    }


  }

  case object EError extends Expr
  case object ESkip extends Expr
  case class EIf private[FSSyntax](a: Pred, p: Expr, q: Expr) extends Expr
  case class ESeq private[FSSyntax](p: Expr, q: Expr) extends Expr
  case class EMkdir private[FSSyntax](path: Path) extends Expr
  case class ECreateFile private[FSSyntax](path: Path, contents: String) extends Expr
  case class ERm private[FSSyntax](path: Path) extends Expr
  case class ECp private[FSSyntax](src: Path, dst: Path) extends Expr

  private val exprCache = scala.collection.mutable.HashMap[Expr, Expr]()

  private val predCache = scala.collection.mutable.HashMap[Pred, Pred]()

  private def internPred(a: Pred) = predCache.getOrElseUpdate(a, a)

  private def intern(e: Expr): Expr = exprCache.getOrElseUpdate(e, e)

  def ite(a: Pred, p: Expr, q: Expr): Expr = {
    if (p eq q) p else intern(EIf(a, p, q))
  }

  def seq(p: Expr, q: Expr) = intern(ESeq(p, q))

  def mkdir(p: Path) = intern(EMkdir(p))

  def createFile(p: Path, c: String) = intern(ECreateFile(p, c))

  def rm(p: Path) = intern(ERm(p))

  def cp(src: Path, dst: Path) = intern(ECp(src, dst))

  def testFileState(p: Path, s: FileState): PTestFileState = internPred(PTestFileState(p, s)).asInstanceOf[PTestFileState]

  def clearCache(): Unit = {
    exprCache.clear()
  }

  object ESeq {
    import Implicits._
    def apply(es: Expr*): Expr = es.foldRight(ESkip: Expr)((e, expr) => e >> expr)
  }

  object PAnd {
    def apply(preds: Pred*): Pred = preds.foldRight[Pred](PTrue) { (x, y) => PAnd(x, y) }
  }

}
