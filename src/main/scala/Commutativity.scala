package rehearsal

private[rehearsal] object Commutativity {

  import java.nio.file.Path
  import FSSyntax._

  /*
   * Take in approx file sets and return exact files sets
   *
   * If there is an overlap between read-write and idempotent
   * set of an expr, then the idempotent op on the intersecting
   * path is not idempotent
   */
  def refinedFileSets(readSet: Set[Path],
                      writeSet: Set[Path],
                      idemSet: Set[Path]): FileSets = {
    val intersection = idemSet intersect (readSet ++ writeSet)
    FileSets(readSet ++ intersection,
             writeSet ++ intersection,
             idemSet diff intersection)
  }

  // Cacluates read, write and Idem sets simultaneously
  def exprFileSets(expr: Expr): FileSets = expr match {
    case Error => FileSets(Set.empty, Set.empty, Set.empty)
    case Skip => FileSets(Set.empty, Set.empty, Set.empty)
    case If(TestFileState(d1, IsDir), Skip, Mkdir(d2)) if d1 == d2 => {
      FileSets(Set.empty, Set.empty, Set(d1))
    }
    case If(TestFileState(d1, DoesNotExist), Mkdir(d2), Skip) if d1 == d2 => {
      FileSets(Set.empty, Set.empty, Set(d1))
    }
    case If(a, p, q) => {
      refinedFileSets(a.readSet ++ p.fileSets.reads ++ q.fileSets.reads,
                      p.fileSets.writes ++ q.fileSets.writes,
                      p.fileSets.dirs ++ q.fileSets.dirs)
    }
    case Seq(p, q) => {
      refinedFileSets(p.fileSets.reads ++ q.fileSets.reads,
                      p.fileSets.writes ++ q.fileSets.writes,
                      p.fileSets.dirs ++ q.fileSets.dirs)
    }
    case Mkdir(path) => {
      if (path.getParent == null) {
        FileSets(Set.empty, Set(path), Set.empty)
      }
      else {
        FileSets(Set(path.getParent), Set(path), Set())
      }
    }
    case CreateFile(path, _) => FileSets(Set.empty, Set(path), Set.empty)
    case Rm(path) => FileSets(Set.empty, Set(path), Set.empty)
    case Cp(src, dst) => FileSets(Set(src), Set(dst), Set.empty)
  }

  def predReadSet(pred: Pred): Set[Path] = pred match {
    case True | False => Set()
    case And(a, b) => a.readSet ++ b.readSet
    case Or(a, b) => a.readSet ++ b.readSet
    case Not(a) => a.readSet
    case TestFileState(path, _) => Helpers.ancestors(path)
    case ITE(a, b, c) => a.readSet ++ b.readSet ++ c.readSet
  }

}
