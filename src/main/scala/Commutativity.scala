package rehearsal

object Commutativity {

  import java.nio.file.Path
  import Implicits._
  import FSSyntax._

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
    case If(a, p, q) => exprFileSets(p).combine(exprFileSets(q)).withReads(a.readSet)
    case Seq(p, q) => exprFileSets(p).combine(exprFileSets(q))
    case Mkdir(path) => {
      if (path.getParent == null) {
        FileSets(Set.empty, Set(path), Set.empty)
      }
      else {
        FileSets(Set(path.getParent), Set(path), Set())
      }
    }
    case CreateFile(path, _) => FileSets(Set(path.getParent), Set(path), Set.empty)
    case Rm(path) => FileSets(Set(path.getParent), Set(path), Set.empty)
    case Cp(src, dst) => FileSets(Set(src), Set(dst), Set.empty)
  }

  def predReadSet(pred: Pred): Set[Path] = pred match {
    case True | False => Set()
    case And(a, b) => a.readSet ++ b.readSet
    case Or(a, b) => a.readSet ++ b.readSet
    case Not(a) => a.readSet
    case TestFileState(path, _) => Set(path)
  }

}
