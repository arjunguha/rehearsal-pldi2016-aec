package rehearsal

object Slicing2 {

  import scala.annotation.tailrec
  import java.nio.file.Path
  import Implicits._
  import FSSyntax._

  def allPathsPred(p: Pred, paths: Set[Path]): Set[Path] = Set()

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
    case If(a, p, q) => allPathsPred(a, paths) union allPaths(p, paths) union allPaths(q, paths)
  }
  
  def slice(paths: Set[Path], e: Expr): Expr = 
    if((allPaths(e, paths) intersect paths) == Set.empty) Skip
    else e
  

}
