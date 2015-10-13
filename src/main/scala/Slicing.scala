package rehearsal

object Slicing {

  import scala.annotation.tailrec
  import java.nio.file.Path
  import Implicits._
  import FSSyntax._
  import scalax.collection.Graph
  import scalax.collection.GraphPredef._

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
    case Rm(f) => paths.filter(p => p.startsWith(f))
    case Cp(src, dst) => Set(src, dst, dst.getParent())
    case Seq(p, q) => allPaths(p, paths) union allPaths(q, paths)
    case If(a, p, q) => allPathsPred(a) union allPaths(p, paths) union allPaths(q, paths)
  }
  
  def slice(e: Expr, paths: Set[Path]): Expr = 
    if((allPaths(e, paths) intersect paths) == Set.empty) Skip
    else e
  
  def interferingPaths(exprs: List[Expr]): Set[Path] = {
    val allPaths = exprs.map(e => Helpers.exprPaths(e))
    val counts = allPaths.flatten.groupBy(identity).mapValues(_.length)
    counts.filter(_._2 > 1).keySet
  }

  def sliceGraph(g: FileScriptGraph): FileScriptGraph = {
    val paths  = interferingPaths(g.exprs.values.map(_.value).toList)
    FSGraph(g.exprs.mapValues(e => slice(e, paths)), g.deps)
  }
}
