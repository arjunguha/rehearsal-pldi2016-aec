package rehearsal

object DeterminismPruning2 {

  import PuppetSyntax.FSGraph
  import Implicits._
  import java.nio.file.Path
  import FSSyntax._

  /**
    * Maps each resource in the map to the set of paths that are accessed only
    * by that resource.
    */
  def pruningCandidates[K](exprs: Map[K, Expr]): Map[K, Set[Path]] = {
    // Maps each path to the number of resources that contain it
    val counts = exprs.values.toSeq.flatMap(_.paths.toSeq)
      .groupBy(identity).mapValues(_.length)
    // All the paths that exist in more than one resource.
    val exclude = counts.filter({ case (_, n) => n > 1 }).keySet
    exprs.mapValues(e => e.paths diff exclude)
  }

  def isDefinitiveWrite(path: Path, expr: Expr): Boolean = {
    val sym = new SymbolicEvaluatorImpl(expr.paths.toList, expr.hashes, Set(), None)

    def test(stat: FileState): Expr = {
      expr >> ite(testFileState(path, stat), Skip, Error)
    }

    sym.everSucceeds(test(IsDir)) ^ sym.everSucceeds(test(IsFile))
  }

  def pruneWrites[K](graph: FSGraph[K]): FSGraph[K] = {
    val candidates = pruningCandidates(graph.exprs).map({
      case (k, paths) => {
        val e = graph.exprs(k)
        (k, paths.filter(p => isDefinitiveWrite(p, e)))
      }
    }).toMap

    val exprs_ = graph.exprs.map {
      case (k, e) => (k, DeterminismPruning.pruneRec(candidates(k), e, Map())._1)
    }.toMap

    graph.copy(exprs = exprs_)
  }

}
