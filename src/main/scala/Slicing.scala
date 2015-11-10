package rehearsal

object Slicing {

  import java.nio.file.Path
  import Implicits._
  import FSSyntax._
  import PuppetSyntax.FSGraph
  import scalax.collection.GraphEdge.DiEdge


  def sliceGraph[K](g: FSGraph[K]): FSGraph[K] = {
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
