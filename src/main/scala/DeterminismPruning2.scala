package rehearsal

import smtlib.parser.CommandsResponses.GetModelResponseSuccess

object DeterminismPruning2 extends com.typesafe.scalalogging.LazyLogging {

  import PuppetSyntax.FSGraph
  import Implicits._
  import java.nio.file.Path
  import FSSyntax._


  /**
    * Maps each resource in the map to the set of paths that are accessed only
    * by that resource. These are candidates for pruning. However, each path
    * P produced by this function can only be pruned if (1) its associated
    * resource may only create a file P or directory P (but not both),
    * (2) no other resources influences P, and (3) P does not influence any
    * other resource.
    */
  def pruningCandidates[K](exprs: Map[K, Expr]): Map[K, Set[Path]] = {
    // Maps each path to the number of resources that contain it
    val counts = exprs.values.toSeq.flatMap(_.paths.toSeq)
      .groupBy(identity).mapValues(_.length)
    // All the paths that exist in more than one resource.
    val exclude = counts.filter({ case (_, n) => n > 1 }).keySet
    exprs.mapValues(e => e.paths diff exclude)
  }

  def isTriviallyFile(path: Path, expr: Expr): Boolean = expr match {
    case CreateFile(p, _) => path == p
    case Mkdir(p) => false
    case Cp(src, _) => false
    case Rm(p) => false
    case Seq(e1, e2) => isTriviallyFile(path, e1) || isTriviallyFile(path, e2)
    case If(pred, e1, e2) =>  isTriviallyFile(path, e1) || isTriviallyFile(path, e2)
    case Skip => false
    case Error => false
  }

  def isDefinitiveWrite(path: Path, expr: Expr): Boolean = {
    val sym = new SymbolicEvaluatorImpl(expr.paths.toList, expr.hashes, Set(), None)

    def test(stat: FileState): Expr = {
      expr >> ite(testFileState(path, stat), Skip, Error)
    }

    sym.everSucceeds(test(IsDir)) ^ sym.everSucceeds(test(IsFile))
  }


  def assertAlwaysFiles(paths: scala.Seq[Path], sym: SymbolicEvaluatorImpl, interSt: rehearsal.ST): Boolean = {
    import smtlib._
    import parser._
    import Commands._
    import Terms._
    import theories.Core.{And => _, Or => _, _}
    import SMT._
    import SMT.Implicits._

    sym.smt.pushPop {
      sym.smt.eval(Assert(Not(interSt.isErr)))
      val term = Or(paths.toSeq.map(p =>
        Not(FunctionApplication("is-IsFile", scala.Seq(interSt.paths(p))))): _*)
      sym.smt.eval(Assert(term))
      val r = !sym.smt.checkSat
      if (!r) {
        val model: List[SExpr] = sym.smt.eval(GetModel()).asInstanceOf[GetModelResponseSuccess].model
        println(sym.stateFromTerm(interSt).getOrElse(throw Unexpected("error for initial state")))
      }
      r
    }
  }

  def prunableSet(candidates: Set[Path], e: Expr): Set[Path] = {
    import smtlib._
    import parser._
    import Commands._
    import Terms._
    import theories.Core.{And => _, Or => _, _}
    import SMT._
    import SMT.Implicits._

    val sym = new SymbolicEvaluatorImpl(e.paths.toList, e.hashes, Set(), None)
    val initSt = sym.initState
    sym.smt.eval(Assert(Not(initSt.isErr)))
    sym.assertPathConsistency(initSt)
    val interSt = sym.evalExpr(initSt, e)

    println("HIHI")
    val (files, otherPaths) = candidates.partition(p => isTriviallyFile(p, e))

    // Forall x . P(x) <=> ! Exist x . !P(x)
    // Forall st . [[ e; file(p1) ]] st != error && ... && [[ e; file(pn) ]] st != error
    // not Exist st . not ([[ e; file(p1) ]] st != error && ... && [[ e; file(pn) ]] st != error)
    // not Exist st . [[ e; file(p1) ]] st != error || ... || [[ e; file(pn) ]] st != error
    for (p <- files.toSeq) {
      if (!assertAlwaysFiles(scala.Seq(p), sym, interSt)) {
        println(s"$p is not a file")
      }
    }

    val filesValid = assertAlwaysFiles(files.toSeq, sym, interSt)

    logger.info(s"filesValid = $filesValid (tried $files)")

      val validPaths = otherPaths.filter { path =>

      def test(stat: FileState): Expr = {
        ite(testFileState(path, stat), Skip, Error)
      }

      val everDir = sym.smt.pushPop {
        logger.info(s"Checking $path can ever be a directory")
        sym.smt.eval(Assert(Not(sym.evalExpr(interSt, test(IsDir)).isErr)))
        sym.smt.checkSat()
      }
      val everFile = sym.smt.pushPop {
        logger.info(s"Checking $path can ever be a file")
        sym.smt.eval(Assert(Not(sym.evalExpr(interSt, test(IsFile)).isErr)))
        sym.smt.checkSat()
      }
      everDir ^ everFile
    }
    if (filesValid) {
      files ++ validPaths
    }
    else {
      logger.info("Not all files were trivially files")
      logger.info(files.toString)
      validPaths
    }
  }

  def pruneWrites[K](graph: FSGraph[K]): FSGraph[K] = {
//    val candidates = pruningCandidates(graph.exprs).map({
//      case (k, paths) => k -> prunableSet(paths, graph.exprs(k))
//    }).toMap
//
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

  def join(s1: Map[Path,TrivialStatus], s2: Map[Path,TrivialStatus]): Map[Path, TrivialStatus] = {
    s1.combine(s2) {
      case (None, None) => throw Unexpected("Should never happen")
      case (Some(x), None) => Some(x)
      case (None, Some(y)) => Some(y)
      case (Some(x), Some(y)) => if (x == y) Some(x) else Some(Unknown)
    }
  }

  def trivialStatus(expr: Expr): Map[Path, TrivialStatus] = expr match {
    case If(_, e1, e2) => join(trivialStatus(e1), trivialStatus(e2))
    case Seq(e1, e2) => join(trivialStatus(e1), trivialStatus(e2))
    case CreateFile(p, _) => Map(p -> OnlyFile)
    case Mkdir(p) => Map(p -> OnlyDirectory)
    case Cp(_, p) => Map(p -> OnlyFile)
    case Rm(_) => Map()
    case Skip => Map()
    case Error => Map()
  }

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

  def branchingPaths(expr: Expr): Set[Path] = expr match {
    case If(pred, e1, e2) => {
      pred.readSet union branchingPaths(e1) union branchingPaths(e2)
    }
    case Seq(e1, e2) => branchingPaths(e1) union branchingPaths(e2)
    case CreateFile(_, _) => Set()
    case Mkdir(_) => Set()
    case Cp(src, _) => Set(src)
    case Rm(_) => Set()
    case Skip => Set()
    case Error => Set()
  }

}
