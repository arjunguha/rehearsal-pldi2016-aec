package rehearsal

object DeterminismPruning extends com.typesafe.scalalogging.LazyLogging   {

  import rehearsal.PuppetSyntax.FSGraph
  import java.nio.file.Path
  import FSSyntax._
  import Implicits._
  import AbstractEval.{EvalLike, StateLike, Stat}

  sealed trait AStat
  case object ADir extends AStat
  case object AFile extends AStat
  case object ADoesNotExist extends AStat
  case object AUntouched extends AStat

  type H = Map[Path, Set[AStat]]

  val allStats = Set[AStat](AFile, ADir, ADoesNotExist)

  def hUnion(h1: Option[H], h2: Option[H]) = (h1, h2) match {
    case (None, _) => h2
    case (_, None) => h1
    case (Some(h1), Some(h2)) => Some(h1.combine(h2) {
      case (None, None) => throw Unexpected("bug in combineMaps")
      case (Some(s1), None) => Some(s1 + AUntouched)
      case (None, Some(s2)) => Some(s2 + AUntouched)
      case (Some(s1), Some(s2)) => Some(s1 union s2)
    })
  }

  case class Abs(f: H => Option[H]) extends StateLike[Abs] {

    def >>(other: Abs) = Abs(st => f(st) match {
      case None => None
      case Some(h) => other.f(h)
    })

    def +(other: Abs) = Abs(st => hUnion(this.f(st), other.f(st)))

    def unary_!(): Abs = Abs(st => f(st) match {
      case None => Some(st.mapValues(_ => allStats))
      case Some(map) => {
        if (map.values.exists(_.size == allStats.size)) {
          None
        }
        else {
          Some(map.mapValues(set => allStats diff set))
        }
      }
    })

  }

  def toAStat(stat: Stat) = stat match {
    case AbstractEval.Dir => ADir
    case AbstractEval.File => AFile
    case AbstractEval.DoesNotExist => ADoesNotExist
  }

  object AEval extends EvalLike {
    type State = Abs

    def test(p: Path, stat: Stat): Abs = {
      val aStat = toAStat(stat)
      Abs(st => st.get(p) match {
        case None => Some(st + (p -> Set(aStat)))
        case Some(set) => {
          if (set.contains(aStat)) {
            Some(st + (p -> Set(aStat)))
          }
          else {
            None
          }
        }
      })
    }

    def set(p: Path, stat: Stat): Abs = Abs(st => Some(st + (p -> Set(toAStat(stat)))))

    val error = Abs(_ => None)

    val skip =  Abs(st => Some(st))
  }

  def absEval(expr: FSSyntax.Expr) = AEval.eval(expr).f(Map())

  def pruneablePaths[A](graph: FSGraph[A]): Set[Path] = {

    //val absStates = graph.exprs.mapValues(absEval)
    val absStates2 = graph.exprs.values.map(absEval)
    val maybeFiles = absStates2.foldLeft[Option[Set[Path]]](Some(Set())) {
      case (None, _) => None
      case (_ ,None) => None
      case (Some(files), Some(st)) => {
        // files that st does not touch
        val preserved = files.filter(p => st.get(p) match {
          case None => true // st does not touch p
          case Some(st) => st == Set(AUntouched)
        })


        val newFiles = st.keySet
          .filter({ case p =>
            st(p).contains(AFile) &&
            (st(p).subsetOf(Set(AFile, AUntouched))) &&
            !files.contains(p) })
        Some(preserved union newFiles)
      }
    }
    assert(maybeFiles.isDefined, "wow-- a static error here")
    maybeFiles.get
  }

  def assertDir(p: Path) = If(TestFileState(p, IsDir), Skip, Error)

  def mayAssertParent(toPrune: Set[Path], p: Path) = {
    if (toPrune.contains(p.getParent)) Skip else assertDir(p.getParent)
  }

  def mkIf(a: Pred, e1: Expr, e2: Expr) = {
    if (e1 == e2) e1 else If(a, e1, e2)
  }

  def pruneExpr(toPrune: Set[Path], expr: Expr): Expr = expr match {
    case Mkdir(p) => {
      if (toPrune.contains(p)) {
        if (toPrune.contains(p.getParent)) Skip else assertDir(p.getParent)
      }
      else {
        expr
      }
    }
    case Error => Error
    case Skip => Skip
    case If(pred, e1, e2) => mkIf(pred,
                                pruneExpr(toPrune, e1),
                                pruneExpr(toPrune, e2))
    case Seq(e1, e2) => pruneExpr(toPrune, e1) >> pruneExpr(toPrune, e2)
    case CreateFile(p, _) => {
      if (toPrune.contains(p)) {
        if (toPrune.contains(p.getParent)) Skip else assertDir(p.getParent)
      }
      else {
        expr
      }
    }
    case Rm(p) =>  if (toPrune.contains(p)) Skip else expr
    case Cp(src, dst) => (toPrune.contains(src), toPrune.contains(dst)) match {
      case (false, false) => expr
      // Since src is read-only and dst is not, we can simply leave cp as-is
      case (true, false) => expr
      case (true, true) => {
        mayAssertParent(toPrune, src) >> mayAssertParent(toPrune, dst)
      }
      case (false, true) => {
        If(TestFileState(src, IsFile), mayAssertParent(toPrune, dst), Error)
      }
    }
  }

  def pruneGraph[A](graph: FSGraph[A]): FSGraph[A] = {
    val toPrune = pruneablePaths(graph)
    logger.info(s"Pruning: $toPrune")
    //val toPrune = toPrune_.filterNot(p => toPrune_.exists(p_ => p_ != p && p_.startsWith(p)))
    logger.info(s"Pruning removes ${toPrune.size} paths")
    FSGraph(graph.exprs.mapValues(e => pruneExpr(toPrune, e)),
            graph.deps)
  }

}
