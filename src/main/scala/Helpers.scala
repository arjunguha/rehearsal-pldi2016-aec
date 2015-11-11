package rehearsal

private[rehearsal] object Helpers {

  import java.nio.file.Path
  import Implicits._
  import FSSyntax._

  def predSize(pred: Pred): Int = pred match {
    case Not(a) => 1 + a.size
    case And(a, b) => 1 + a.size + b.size
    case Or(a, b) => 1 + a.size + b.size
    case TestFileState(_, _) => 1
    case True => 1
    case False => 1
  }

  def size(expr: Expr): Int = expr match {
    case Error => 1
    case Skip => 1
    case If(a, p, q) => 1 + a.size + p.size + q.size
    case Seq(p, q) => 1 + p.size + q.size
    case Mkdir(_) => 1
    case CreateFile(_, _) => 1
    case Rm(_) => 1
    case Cp(_, _) => 1
  }

  def ancestors(path: Path): Set[Path] = {
    if (path.getParent == null) {
      Set(path)
    }
    else {
      //TODO(jcollard): The comment on this was reversed when I found it
      // I am assuming there was some reason for it but I cannot figure it out.
      //Set(path, path.getParent)
      ancestors(path.getParent) + path
    }
  }

  def exprPaths(expr: Expr): Set[Path] = expr match {
    case Error => Set()
    case Skip => Set()
    case If(a, p, q) => a.readSet union exprPaths(p) union exprPaths(q)
    case Seq(p, q) => exprPaths(p) union exprPaths(q)
    case Mkdir(f) => ancestors(f)
    case CreateFile(f, _) => ancestors(f)
    case Rm(f) => ancestors(f)
    case Cp(src, dst) => ancestors(src) union ancestors(dst)
  }

  def exprHashes(expr: Expr): Set[String] = expr match{
    case Error => Set()
    case Skip => Set()
    case If(a, p, q) => p.hashes union q.hashes
    case Seq(p, q) => p.hashes union q.hashes
    case Mkdir(f) => Set()
    case CreateFile(f, h) => Set(h)
    case Rm(f) => Set()
    case Cp(src, dst) => Set()
  }


}
