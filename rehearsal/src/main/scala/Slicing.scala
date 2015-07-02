package rehearsal

object Slicing {

  import scala.annotation.tailrec
  import java.nio.file.Path
  import Implicits._
  import FSSyntax._

  /*

   In these examples, we are trying to calculate the paths that affect /target:

   /a affects, but /b does not affect

   if (dir(/a)) {
     mkdir(/b)
     mkdir(/target)
   }

   mkdir(/c);
   if (dir(/c)) { mkdir(/a) } else { skip };
   if (dir(/a)) { mkdir(/target) } else { skip }

   */

  // dep(paths, expr) produces the set of paths in [expr] whose state immediately affects the state of the
  // paths in paths.
  def dep(paths: Set[Path], expr: Expr): Set[Path] = expr match {
    case Error => Set()
    case Skip => Set()
    case Seq(p, q) => dep(paths, p) union dep(paths, q)
    case Mkdir(f) => if (paths.exists(p => p.startsWith(f))) { Set(f) } else { Set() }
    case Rm(f) => if (paths.exists(p => p.startsWith(f))) { Set(f) } else { Set() }
    case CreateFile(f, _) => if (paths.exists(p => p.startsWith(f))) { Set(f) } else { Set() }
    case Cp(src, dst) => {
      // Could be more precise?
      if (paths.exists(p => p.startsWith(src) || p.startsWith(dst))) { Set(src, dst) } else { Set() }
    }
    case If(a, p, q) => {
      val affected = dep(paths, p) union dep(paths, q)
      if (affected.isEmpty) {
        Set()
      }
      else {
        affected union a.readSet
      }
    }
  }

  @tailrec
  def allDeps(paths: Set[Path], expr: Expr): Set[Path] = {
    val newDeps = dep(paths, expr)
    if (newDeps.subsetOf(paths)) {
      paths
    }
    else {
      allDeps(newDeps union paths, expr)
    }
  }

  def sliceRec(paths: Set[Path], expr: Expr): Expr = expr match {
    case Error => Error
    case Skip => Skip
    case Seq(p, q) => sliceRec(paths, p) >> sliceRec(paths, q)
    case Rm(f) => {
      val descendants = paths.filter(p => p != f && p.startsWith(f))
      if (paths.contains(f) || !descendants.isEmpty) expr else Skip
    }
    case Mkdir(f) => if (paths.contains(f) || paths.contains(f.getParent)) expr else Skip
    case CreateFile(f, _)  => if (paths.contains(f) || paths.contains(f.getParent)) expr else Skip
    case Cp(src, dst) => if (paths.contains(src) || paths.contains(dst) || 
        paths.contains(dst.getParent)) expr else Skip
    case If(a, p, q) => {
      val p2 = sliceRec(paths, p)
      val q2 = sliceRec(paths, q)
      if(p2 == q2) p2 else If(a, p2, q2)
    }
  }

  def slice(paths: Set[Path], expr: Expr): Expr = sliceRec(allDeps(paths, expr), expr)

  def interferingPaths(exprs: List[Expr]): Set[Path] = {
    val allPaths = exprs.map(e => Helpers.exprPaths(e))
    val counts = allPaths.flatten.groupBy(identity).mapValues(_.length)
    counts.filter(_._2 > 1).keySet
  }

  def sliceGraph(g: FileScriptGraph): FileScriptGraph = {
    import scalax.collection.Graph, scalax.collection.GraphPredef._

    val paths  = interferingPaths(g.nodes.map(_.value).toList)
    val map = g.nodes.map(p => p -> slice(paths, p)).toMap
    val edges = g.edges.map(edge => map(edge.from) ~> map(edge.to))
    val nodes = map.values
    Graph.from(nodes, edges)
  }

}
