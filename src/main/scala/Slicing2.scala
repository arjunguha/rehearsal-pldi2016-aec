package rehearsal

object Slicing2 {

  import scala.annotation.tailrec
  import java.nio.file.Path
  import Implicits._
  import FSSyntax._

  def allPathsPred(p: Pred): Set[Path] = p match {
    case True | False => Set()
    case And(a, b) => allPathsPred(a) union allPathsPred(b)
    case Or(a, b) => allPathsPred(a) union allPathsPred(b)
    case Not(a) => allPathsPred(a)
    case TestFileState(p, _) => Set(p)
    case ITE(a, b, c) => allPathsPred(a) union allPathsPred(b) union allPathsPred(c)
  }
  

  def allPaths(e: Expr, paths: Set[Path]): Set[Path] = e match {
    case Error | Skip => Set()
    case Mkdir(p) => Set(p, p.getParent())
    case CreateFile(p, _) => Set(p, p.getParent())
    case Rm(f) => {
      val descendants = paths.filter(p => p != f && p.startsWith(f))
      descendants union Set(f)
    }
    case Cp(src, dst) => Set(src, dst, dst.getParent())
    case Seq(p, q) => allPaths(p, paths) union allPaths(q, paths)
    case If(a, p, q) => allPathsPred(a) union allPaths(p, paths) union allPaths(q, paths)
  }
  
  def slice(paths: Set[Path], e: Expr): Expr = 
    if((allPaths(e, paths) intersect paths) == Set.empty) Skip
    else e
  

}
