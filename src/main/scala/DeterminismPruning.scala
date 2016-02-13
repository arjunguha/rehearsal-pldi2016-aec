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
          (ite(testFileState(p.getParent, IsDir),
              Skip, Error),
           h + (p -> ADir) + (p.getParent -> ADir))
        case Mkdir(p) => (e, h + (p -> ADir) + (p.getParent -> ADir))
        case CreateFile(p, _) if canPrune.contains(p) =>
          (ite(testFileState(p.getParent, IsDir),
              Skip, Error),
           h + (p -> AFile) + (p.getParent -> ADir))
        case CreateFile(p, _) => (e, h + (p -> AFile) + (p.getParent -> ADir))
        /*TODO [Rian]: this only prunes RmFiles not RmDirs; need IsEmpty predicate*/
        case Rm(p) if canPrune.contains(p) => (Skip,
                                        h + (p -> ADoesNotExist))
        case Rm(_) => (e, h)
        case Cp(p1, p2) if canPrune.contains(p2) =>
          (ite(testFileState(p1, IsFile) &&
                testFileState(p2.getParent, IsDir),
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
