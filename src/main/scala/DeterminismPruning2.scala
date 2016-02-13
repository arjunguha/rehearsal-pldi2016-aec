package rehearsal

import smtlib.parser.CommandsResponses.GetModelResponseSuccess

object DeterminismPruning2 extends com.typesafe.scalalogging.LazyLogging {

  import PuppetSyntax.FSGraph
  import Implicits._
  import java.nio.file.Path
  import FSSyntax._

  def pruneWrites[K](graph: FSGraph[K]): FSGraph[K] = {
    val candidates = pruningCandidates2(graph.exprs)
    val exprs_ = graph.exprs.map {
      case (k, e) => (k, DeterminismPruning.pruneRec(candidates(k), e, Map())._1)
    }.toMap

    graph.copy(exprs = exprs_)
  }

  sealed trait TrivialStatus
  case object OnlyFile extends TrivialStatus
  case object OnlyDirectory extends TrivialStatus
  case object Unknown extends TrivialStatus

  def join2(branching: Set[Path], s1: Map[Path,(Set[Path], TrivialStatus)],
            s2: Map[Path,(Set[Path], TrivialStatus)]): Map[Path,(Set[Path], TrivialStatus)] = {
    s1.combine(s2) {
      case (None, None) => throw Unexpected("Should never happen")
      case (Some((set, x)), None) => Some((branching union set, x))
      case (None, Some((set, x))) => Some((branching union set, x))

      case (Some((set1, x)), Some((set2, y))) => if (x == y) Some((set1 union set2, x)) else Some((Set(), Unknown))
    }
  }

  def trivialStatus2(expr: Expr): Map[Path, (Set[Path], TrivialStatus)] = expr match {
    case If(pred, e1, e2) => join2(pred.readSet, trivialStatus2(e1), trivialStatus2(e2))
    case Seq(e1, e2) => join2(Set(), trivialStatus2(e1), trivialStatus2(e2))
    case CreateFile(p, _) => Map(p -> (Set(p), OnlyFile))
    case Mkdir(p) => Map(p -> (Set(p), OnlyDirectory))
    case Cp(_, p) => Map(p -> (Set(p), OnlyFile))
    case Rm(_) => Map()
    case Skip => Map()
    case Error => Map()
  }

  def definitiveWrites(exclude: Set[Path], expr: Expr): scala.Seq[Path] = {
    trivialStatus2(expr).toSeq.filter({ case (_, (reads, status)) => status != Unknown && reads.intersect(exclude).isEmpty } ).map(_._1)
  }

  def candidates[K](exprs: Map[K, Expr]): Map[K, Set[Path]] = {
    // Maps each path to the number of resources that contain it
    val counts = exprs.values.toSeq.flatMap(_.paths.toSeq)
      .groupBy(identity).mapValues(_.length)
    // All the paths that exist in more than one resource.
    val exclude = counts.filter({ case (_, n) => n > 1 }).keySet
    exprs.mapValues(e => e.paths diff exclude)
  }

  def pruningCandidates2[K](exprs: Map[K, Expr]): Map[K, Set[Path]] = {
    val counts = exprs.values.toSeq.flatMap(_.paths.toSeq)
      .groupBy(identity).mapValues(_.length)
    // All the paths that exist in more than one resource.
    val exclude = counts.filter({ case (_, n) => n > 1 }).keySet

    val candidateMap = candidates(exprs)
    val gen = for ((res, expr) <- exprs) yield {
      val definitive = definitiveWrites(exclude, expr)
      val noninterfering = definitive.toSet intersect candidateMap(res)
      (res, noninterfering)
    }
    gen.toMap
  }
}
