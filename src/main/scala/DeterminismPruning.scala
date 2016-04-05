package rehearsal

object DeterminismPruning2 extends com.typesafe.scalalogging.LazyLogging {

  import FSSyntax._
  import Implicits._

  def pruneWrites[K](graph: FSGraph[K]): FSGraph[K] = {
    val rws = graph.exprs.mapValues(e => (e.fileSets.reads, e.fileSets.writes union e.fileSets.dirs))
    /* If a resource definitively writes to a location that its successors only read
       then those reads can be specialized to account for the effect of this definitive write.


       In these cases:

       - mkdir(p); e1 =? mkdir(p); e2
       - if (dir?(p)) then skip else mkdir(p); e1 =? if (dir?(p)) then skip else mkdir(p); e2
       - and so on

       e1 and e2 can be specialized to assume that p is a directory

       Another case:

       Suppose we are asking:

        e; if (pred) then mkdir(p) else skip; e1 =? e; if (pred) then mkdir(p) else skip; ; e2

        and neither e, e1, nor, e2 can read or write to p.

        If e does not influence the truth or falsity of pred we can instead write:

        if (pred) then mkdir(p) else





    */

    // If R writes to a path p and (1) resources that may-happen-after R do not read or write to p
    // and (2) resources that may-happen-before R make the same definite write to paths that
    // may influence p, then the write to p in R can be pruned.
    // the write

    val stats = graph.exprs.keys.map(k => k -> DeterminismPruning.trivialStatus(graph.exprs(k))).toMap

    def propagateWrites(exprs: Map[K, Expr], label: K): Map[K, Expr] = {
      val stat = stats(label)
      val succs = graph.deps.descendants(graph.deps.get(label)).map(_.value)
      val definiteWrites = stat.filter({ case (_, (_, status)) => status != DeterminismPruning.Unknown })
        .mapValues(_._2)

      val pushableWrites = definiteWrites.filterKeys(p =>
        succs.forall(k =>
          !exprs(k).fileSets.writes().contains(p) && !exprs(k).fileSets.dirs().contains(p)))

      val heap = pushableWrites.mapValues {
        case DeterminismPruning.OnlyFile => DeterminismPruning.AFile
        case DeterminismPruning.OnlyDirectory => DeterminismPruning.ADir
        case DeterminismPruning.Unknown => ???
      }

      exprs.mapIf(k => succs.contains(k),
        e => DeterminismPruning.pruneRec(Set(), e, heap)._1)
    }

    graph.copy(exprs = graph.exprs.keySet.foldLeft(graph.exprs)(propagateWrites))
  }

}

object DeterminismPruning extends com.typesafe.scalalogging.LazyLogging   {

  import FSSyntax._
  import Implicits._

  sealed trait AStat {
    def ==(other: FileState): Boolean = (this, other) match {
      case (ADir, IsDir) => true
      case (AFile, IsFile) => true
      case (ADoesNotExist, DoesNotExist) => true
      case _ => false
    }
  }
  case object ADir extends AStat
  case object AFile extends AStat
  case object ADoesNotExist extends AStat
  case object AUntouched extends AStat

  def specPred(pred: Pred, h: Map[Path, AStat]): Pred = pred match {
    case PTestFileState(p, s) => {
      if (!h.contains(p)) {
        pred
      }
      else {
        if (h(p) == s) PTrue else PFalse
      }
    }
    case PTrue | PFalse => pred
    case POr(e1, e2) => specPred(e1, h) || specPred(e2, h)
    case PAnd(e1, e2) => specPred(e1, h) && specPred(e2, h)
    case PNot(e) => !specPred(e, h)
  }

  def pruneRec(canPrune: Set[Path], e: Expr, h: Map[Path, AStat]):
    (Expr, Map[Path, AStat]) = {
      e match {
        case ESkip => (e, h)
        case EError => (e, h)
        case EMkdir(p) if canPrune.contains(p) =>
          (ite(testFileState(p.getParent, IsDir),
              ESkip, EError),
           h + (p -> ADir) + (p.getParent -> ADir))
        case EMkdir(p) => (e, h + (p -> ADir) + (p.getParent -> ADir))
        case ECreateFile(p, _) if canPrune.contains(p) =>
          (ite(testFileState(p.getParent, IsDir),
              ESkip, EError),
           h + (p -> AFile) + (p.getParent -> ADir))
        case ECreateFile(p, _) => (e, h + (p -> AFile) + (p.getParent -> ADir))
        /*TODO [Rian]: this only prunes RmFiles not RmDirs; need IsEmpty predicate*/
        case ERm(p) if canPrune.contains(p) => (ESkip,
                                        h + (p -> ADoesNotExist))
        case ERm(_) => (e, h)
        case ECp(p1, p2) if canPrune.contains(p2) =>
          (ite(testFileState(p1, IsFile) &&
                testFileState(p2.getParent, IsDir),
              ESkip, EError),
           h + (p1 -> AFile) + (p2 -> AFile) + (p2.getParent -> ADir))
        case ECp(p1, p2) => (e, h + (p1 -> AFile) + (p2 -> AFile) + (p2.getParent -> ADir))
        case ESeq(e1, e2) => {
          val e1Pruned = pruneRec(canPrune, e1, h)
          val e2Pruned = pruneRec(canPrune, e2, h ++ e1Pruned._2)
          (e1Pruned._1 >> e2Pruned._1, e2Pruned._2)
        }
        case EIf(a, e1, e2) => {
          val e1Pruned = pruneRec(canPrune, e1, h)
          val e2Pruned = pruneRec(canPrune, e2, h)
          (ite(specPred(a, h), e1Pruned._1, e2Pruned._1), h)
        }
      }
    }

  sealed trait TrivialStatus
  case object OnlyFile extends TrivialStatus
  case object OnlyDirectory extends TrivialStatus
  case object Unknown extends TrivialStatus

  def prune(canPrune: Set[Path], e: Expr): Expr = {
    val result = pruneRec(canPrune, e, Map())._1
    //assert (result.paths.intersect(canPrune).isEmpty, s"pruning did not remove path: $result")
    result
  }

  def join(branching: Set[Path],
           s1: Map[Path,(Set[Path], TrivialStatus)],
           s2: Map[Path,(Set[Path], TrivialStatus)]): Map[Path,(Set[Path], TrivialStatus)] = {
    s1.combine(s2) {
      case (None, None) => throw Unexpected("Should never happen")
      case (Some((set, x)), None) => Some((branching union set, x))
      case (None, Some((set, x))) => Some((branching union set, x))

      case (Some((set1, x)), Some((set2, y))) =>  Some((branching union set1 union set2, if (x == y) x else Unknown))
    }
  }

  // Map each path to the set of paths that affect its state and an abstact value
  // that summarizes the state of the path.
  def trivialStatus(expr: Expr): Map[Path, (Set[Path], TrivialStatus)] = expr match {
    case EIf(pred, e1, e2) => join(pred.readSet, trivialStatus(e1), trivialStatus(e2))
    case ESeq(e1, e2) => join(Set(), trivialStatus(e1), trivialStatus(e2))
    case ECreateFile(p, _) => Map(p -> (Set(p), OnlyFile))
    case EMkdir(p) => Map(p -> (Set(p), OnlyDirectory))
    case ECp(_, p) => Map(p -> (Set(p), OnlyFile))
    case ERm(_) => Map()
    case ESkip => Map()
    case EError => Map()
  }

  // If a path is definitely written and is not affected by the state of paths
  // that appear in other resources, we can prune them.
  def definitiveWrites(exclude: Set[Path], expr: Expr): scala.Seq[Path] = {
    trivialStatus(expr).toSeq.filter({ case (_, (reads, status)) => reads.intersect(exclude).isEmpty } ).map(_._1)
  }

  def pruningCandidates[K](exprs: Map[K, Expr]): Map[K, Set[Path]] = {
    val counts = exprs.values.toSeq.flatMap(_.paths.toSeq)
      .groupBy(identity).mapValues(_.length)
    // All the paths that exist in more than one resource.
    val exclude = counts.filter({ case (_, n) => n > 1 }).keySet

    val candidateMap = exprs.mapValues(e => e.paths diff exclude)
    val gen = for ((res, expr) <- exprs) yield {
      val definitive = definitiveWrites(exclude, expr)
      val noninterfering = definitive.toSet intersect candidateMap(res)
      (res, noninterfering)
    }
    gen.toMap
  }

  def removeUnobservableWrites[K](graph: FSGraph[K]): FSGraph[K] = {
    val candidates = pruningCandidates(graph.exprs)
    val exprs_ = graph.exprs.map {
      case (k, e) => (k, DeterminismPruning.pruneRec(candidates(k), e, Map())._1)
    }.toMap

    graph.copy(exprs = exprs_)
  }

  def pruneWrites[K](graph: FSGraph[K]): FSGraph[K] = {
    removeUnobservableWrites(graph)
  }

}
