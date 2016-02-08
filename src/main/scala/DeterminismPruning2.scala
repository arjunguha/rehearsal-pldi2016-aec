package rehearsal

object DeterminismPruning2 extends com.typesafe.scalalogging.LazyLogging {

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

  def isTriviallyFile(path: Path, expr: Expr): Boolean = expr match {
    case CreateFile(_, _) => true
    case Mkdir(p) => path != p
    case Cp(src, _) => path != src
    case Rm(p) => path != p
    case Seq(e1, e2) => isTriviallyFile(path, e1) && isTriviallyFile(path, e2)
    case If(pred, e1, e2) => !pred.readSet.contains(path) && isTriviallyFile(path, e1) && isTriviallyFile(path, e2)
    case Skip => true
    case Error => true
  }

  def pruneWrites[K](graph: FSGraph[K]): FSGraph[K] = {
    import smtlib._
    import parser._
    import Commands._
    import Terms._
    import theories.Core.{And => _, Or => _, _}

    val candidates = pruningCandidates(graph.exprs).map({
      case (k, paths) => {
        logger.info(s"${paths.size} candidate paths for $k")

        val e = graph.exprs(k)
        val sym = new SymbolicEvaluatorImpl(e.paths.toList, e.hashes,
          Set(), None)
        val initSt = sym.initState
        sym.smt.eval(Assert(Not(initSt.isErr)))
        sym.assertPathConsistency(initSt)
        val interSt = sym.evalExpr(initSt, e)

        val (files, otherPaths) = paths.partition(p => isTriviallyFile(p, e))

        val validPaths = otherPaths.filter { path =>

          def test(stat: FileState): Expr = {
            ite(testFileState(path, stat), Skip, Error)
          }

          val everDir = sym.smt.pushPop {
            sym.smt.eval(Assert(Not(sym.evalExpr(interSt, test(IsDir)).isErr)))
            sym.smt.checkSat()
          }
          val everFile = sym.smt.pushPop {
            sym.smt.eval(Assert(Not(sym.evalExpr(interSt, test(IsDir)).isErr)))
            sym.smt.checkSat()
          }
          everDir ^ everFile
        }
        (k, files ++ validPaths)
      }
    }).toMap

    val exprs_ = graph.exprs.map {
      case (k, e) => (k, DeterminismPruning.pruneRec(candidates(k), e, Map())._1)
    }.toMap

    graph.copy(exprs = exprs_)
  }

}
