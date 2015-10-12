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
    case Rm(f) => {
      val descendants = paths.filter(p => p != f && p.startsWith(f))
      descendants union Set(f)
    }
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

  def sliceGraph(g: FileScriptGraph): FileScriptGraph = { Graph()
    //TODO: (Rian) Get set of all paths that appear in more than one node of G
    val paths  = interferingPaths(g.nodes.map(_.value).toList)
    val nodes = g.nodes.map(p => slice(p, paths))
    val edges = g.edges.map(e => slice(e.from, paths) ~> slice(e.to, paths))
    Graph.from(nodes, edges)
  }
}
