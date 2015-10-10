package rehearsal

object Slicing {

  import scala.annotation.tailrec
  import java.nio.file.Path
  import Implicits._
  import FSSyntax._

  def allPaths(e: Expr, paths: Set[Path]): Set[Path] = e match {
    case Error | Skip => Set()
    case Mkdir(p) => Set(p, p.parent)
    case CreateFile(p, _) => Set(p, p.parent)
    case Rm(p) => {
      val descendants = paths.filter(p => p != f && p.startsWith(f))
      descendants union Set(p)
    }
    case Cp(src, dst) => Set(src, src.parent, dst, dst.parent)
    case Seq(p, q) => allPaths(p) union allPaths(q)
    case If(a, p, q) => allPathsPred(a) union allPaths(p) union allPaths(q)
  }
  

}
