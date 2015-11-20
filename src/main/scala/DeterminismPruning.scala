package rehearsal

object DeterminismPruning extends com.typesafe.scalalogging.LazyLogging   {

  import rehearsal.PuppetSyntax.FSGraph
  import java.nio.file.Path
  import FSSyntax._
  import Implicits._
  import AbstractEval.{EvalLike, StateLike, Stat}

  sealed trait AStat {
    def ==(other: FileState): Boolean = (this, other) match {
      case (ADir, IsDir) => true
      case (AFile, IsFile) => true
      case (ADoesNotExist, DoesNotExist) => true
      case _ => false
    }
  }
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

  def specPred(pred: Pred, h: Map[Path, AStat]): Pred = pred match {
    case TestFileState(p, s) => {
      if (!h.contains(p)) {
        pred
      }
      else {
        if (h(p) == s) True else False
      }
    }
    case True | False => pred
    case Or(e1, e2) => specPred(e1, h) || specPred(e2, h)
    case And(e1, e2) => specPred(e1, h) && specPred(e2, h)
    case Not(e) => !specPred(e, h)
  }

  def pruneRec(canPrune: Set[Path], e: Expr, h: Map[Path, AStat]):
    (Expr, Map[Path, AStat]) = {
      e match {
        case Skip => (e, h)
        case Error => (e, h)
        case Mkdir(p) if canPrune.contains(p) =>
          (If(TestFileState(p, DoesNotExist) && TestFileState(p.getParent, IsDir),
              Skip, Error),
           h + (p -> ADir) + (p.getParent -> ADir))
        case Mkdir(p) => (e, h + (p -> ADir) + (p.getParent -> ADir))
        case CreateFile(p, _) if canPrune.contains(p) =>
          (If(TestFileState(p, DoesNotExist) && TestFileState(p.getParent, IsDir),
              Skip, Error),
           h + (p -> AFile) + (p.getParent -> ADir))
        case CreateFile(p, _) => (e, h + (p -> AFile) + (p.getParent -> ADir))
        /*TODO [Rian]: this only prunes RmFiles not RmDirs; need IsEmpty predicate*/
        case Rm(p) if canPrune.contains(p) => (If(!TestFileState(p, IsFile), Skip, Error),
                                        h + (p -> ADoesNotExist))
        case Rm(_) => (e, h)
        case Cp(p1, p2) if canPrune.contains(p2) =>
          (If(TestFileState(p1, IsFile) && TestFileState(p2, DoesNotExist) &&
                TestFileState(p2.getParent, IsDir),
              Skip, Error),
           h + (p1 -> AFile) + (p2 -> AFile) + (p2.getParent -> ADir))
        case Cp(p1, p2) => (e, h + (p1 -> AFile) + (p2 -> AFile) + (p2.getParent -> ADir))
        case Seq(e1, e2) => {
          val e1Pruned = pruneRec(canPrune, e1, h)
          val e2Pruned = pruneRec(canPrune, e2, h ++ e1Pruned._2)
          (e1Pruned._1 >> e2Pruned._1, e2Pruned._2)
        }
        case If(a, e1, e2) => {
          val e1Pruned = pruneRec(canPrune, e1, h)
          val e2Pruned = pruneRec(canPrune, e2, h)
          (If(specPred(a, h), e1Pruned._1, e2Pruned._1), h)
        }
      }
    }

  def prune(canPrune: Set[Path], e: Expr): Expr = pruneRec(canPrune, e, Map())._1

  def pruneGraph[A](graph: FSGraph[A]): FSGraph[A] = {
    val toPrune = pruneablePaths(graph)
    logger.info(s"Pruning: $toPrune")
    //val toPrune = toPrune_.filterNot(p => toPrune_.exists(p_ => p_ != p && p_.startsWith(p)))
    logger.info(s"Pruning removes ${toPrune.size} paths")
    FSGraph(graph.exprs.mapValues(e => prune(toPrune, e)), graph.deps)
  }

  def pruneablePathCount[A](graph: FSGraph[A]): Int = pruneablePaths(graph).size

}
