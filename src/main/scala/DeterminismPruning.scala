package rehearsal

object DeterminismPruning extends com.typesafe.scalalogging.LazyLogging   {

  import rehearsal.PuppetSyntax.FSGraph
  import java.nio.file.Path
  import FSSyntax._
  import Implicits._

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

  def specPred(pred: Pred, h: Map[Path, AStat]): Pred = pred match {
    case PTestFileState(p, s) => {
      if (!h.contains(p)) {
        pred
      }
      else {
        if (h(p) == s) PTrue else PFalse
      }
    }
    case PTrue | PFalse => pred
    case POr(e1, e2) => specPred(e1, h) || specPred(e2, h)
    case PAnd(e1, e2) => specPred(e1, h) && specPred(e2, h)
    case PNot(e) => !specPred(e, h)
  }

  def pruneRec(canPrune: Set[Path], e: Expr, h: Map[Path, AStat]):
    (Expr, Map[Path, AStat]) = {
      e match {
        case ESkip => (e, h)
        case EError => (e, h)
        case EMkdir(p) if canPrune.contains(p) =>
          (ite(testFileState(p.getParent, IsDir),
              ESkip, EError),
           h + (p -> ADir) + (p.getParent -> ADir))
        case EMkdir(p) => (e, h + (p -> ADir) + (p.getParent -> ADir))
        case ECreateFile(p, _) if canPrune.contains(p) =>
          (ite(testFileState(p.getParent, IsDir),
              ESkip, EError),
           h + (p -> AFile) + (p.getParent -> ADir))
        case ECreateFile(p, _) => (e, h + (p -> AFile) + (p.getParent -> ADir))
        /*TODO [Rian]: this only prunes RmFiles not RmDirs; need IsEmpty predicate*/
        case ERm(p) if canPrune.contains(p) => (ESkip,
                                        h + (p -> ADoesNotExist))
        case ERm(_) => (e, h)
        case ECp(p1, p2) if canPrune.contains(p2) =>
          (ite(testFileState(p1, IsFile) &&
                testFileState(p2.getParent, IsDir),
              ESkip, EError),
           h + (p1 -> AFile) + (p2 -> AFile) + (p2.getParent -> ADir))
        case ECp(p1, p2) => (e, h + (p1 -> AFile) + (p2 -> AFile) + (p2.getParent -> ADir))
        case ESeq(e1, e2) => {
          val e1Pruned = pruneRec(canPrune, e1, h)
          val e2Pruned = pruneRec(canPrune, e2, h ++ e1Pruned._2)
          (e1Pruned._1 >> e2Pruned._1, e2Pruned._2)
        }
        case EIf(a, e1, e2) => {
          val e1Pruned = pruneRec(canPrune, e1, h)
          val e2Pruned = pruneRec(canPrune, e2, h)
          (ite(specPred(a, h), e1Pruned._1, e2Pruned._1), h)
        }
      }
    }

  def prune(canPrune: Set[Path], e: Expr): Expr = {
    val result = pruneRec(canPrune, e, Map())._1
    //assert (result.paths.intersect(canPrune).isEmpty, s"pruning did not remove path: $result")
    result
  }

  def pruneGraph[A](graph: FSGraph[A]): FSGraph[A] = DeterminismPruning2.pruneWrites(graph)

}
