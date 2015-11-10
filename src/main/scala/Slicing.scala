package rehearsal

object Slicing {

  import scala.annotation.tailrec
  import java.nio.file.Path
  import Implicits._
  import FSSyntax._
  import PuppetSyntax.{FSGraph, FileScriptGraph, Node}
  import scalax.collection.Graph
  import scalax.collection.GraphPredef._
  import scalax.collection.GraphEdge.DiEdge

  def slice(e: Expr, paths: Set[Path]): Expr = e match {
    case Skip | Error => e
    case Mkdir(p) => if (paths.contains(p) || paths.contains(p.getParent)) e
                     else Skip
    case CreateFile(p, _) => if (paths.contains(p) || paths.contains(p.getParent)) e
                             else Skip
    case Rm(p) => if(paths.exists(_.startsWith(p))) e
                  else Skip
    case Cp(p1, p2) => 
      if(paths.contains(p1) || paths.contains(p2) || paths.contains(p2.getParent)) e
      else Skip
    case Seq(p, q) =>{ 
      val pSliced = slice(p, paths)
      val qSliced = slice(q, paths)
      if(pSliced == Skip) qSliced
      else if(qSliced == Skip) pSliced
      else Seq(pSliced, qSliced)
    }
    case If(a, p, q) => {
      val pSliced = slice(p, paths)
      val qSliced = slice(q, paths)
      if(pSliced == qSliced) pSliced
      else                   If(a, pSliced, qSliced)
    }
  }  

  def interferingPaths(exprs: List[Expr]): Set[Path] = {
    val allPaths = exprs.map(e => Helpers.exprPaths(e))
    val counts = allPaths.flatten.groupBy(identity).mapValues(_.length)
    counts.filter(_._2 > 1).keySet
  }

  def sliceGraph[K](g: FSGraph[K]): FSGraph[K] = {
    val paths  = interferingPaths(g.exprs.values.map(_.value).toList)
    //val newG = FSGraph(g.exprs.mapValues(e => slice(e, paths)).view.force, g.deps)
    val newG = DeterminismPruning2.pruneGraph(g)
    val diff = g.exprs.filterKeys(k => newG.exprs(k) == Skip).keySet
    diff.foldRight(newG)(skipSkips)
  }

  def skipSkips[K](useless: K, g: FSGraph[K]): FSGraph[K] = {
    val in = g.deps.get(useless).incoming.map(_.head.value)
    val out = g.deps.get(useless).outgoing.map(_.last.value)
    val newEdges = in.foldRight(Set[DiEdge[K]]())({ case (i, set) => set union out.map(o => DiEdge(i, o)) })
    FSGraph(g.exprs - useless, g.deps - useless)
  }
}
