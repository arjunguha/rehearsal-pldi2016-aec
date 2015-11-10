package rehearsal

object DeterminismPruning2 extends com.typesafe.scalalogging.LazyLogging   {

  import rehearsal.PuppetSyntax.FSGraph
  import java.nio.file.Path
  import FSSyntax._
  import Implicits._

  sealed trait Stat
  case object AIsFile extends Stat
  case object AIsDir extends Stat
  case object ADoesNotExist extends Stat

  val allStat = Known(Set(AIsFile, AIsDir, ADoesNotExist))

  sealed trait A {

    def >>(other: A): A = (this, other) match {
      case (ABot, x) => x
      case (x, ABot) => x
      case (Known(set1), Known(set2)) => other
    }

    def +(other: A): A = (this, other) match {
      case (ABot, y) => y
      case (x, ABot) => x
      case (Known(set1), Known(set2)) => Known(set1 union set2)
    }

    def ||(other: A): A = (this, other) match {
      case (ABot, y) => y
      case (x, ABot) => x
      case _ => allStat

    }
  }

  case class Known(set: Set[Stat]) extends A
  case object ABot extends A

  def combineMaps[A, B, C, D](m1: Map[A, B], m2: Map[A, C])(f: (Option[B], Option[C]) => Option[D]) = {
    val keys = m1.keySet ++ m2.keySet
    keys.foldLeft(Map[A,D]())({ case (map, k) =>
      f(m1.get(k), m2.get(k)) match {
        case None => map
        case Some(v) => map + (k -> v)
      }
    })
  }


  case class AbstractState(map: Option[Map[Path, A]]) {

    def >>(other: AbstractState): AbstractState = {
      val m = (this.map, other.map) match {
        case (None, _) => None
        case (_, None) => None
        case (Some(m1), Some(m2)) =>
          Some(combineMaps(m1, m2)((x, y) => Some(x.getOrElse(ABot) >> y.getOrElse(ABot))))
      }

      AbstractState(m)
    }

    def +(other: AbstractState): AbstractState = {
      AbstractState((this.map, other.map) match {
        case (None, m2) => m2
        case (m1, None) => m1
        case (Some(m1), Some(m2)) =>
          Some(combineMaps(m1, m2)((x, y) =>  Some(x.getOrElse(ABot) + y.getOrElse(ABot))))
      })
    }

    def ||(other: AbstractState): AbstractState = {
      AbstractState((this.map, other.map) match {
        case (None, m2) => m2
        case (m1, None) => m1
        case (Some(m1), Some(m2)) =>
          Some(combineMaps(m1, m2)((x, y) =>  Some(x.getOrElse(ABot) || y.getOrElse(ABot))))
      })
    }

  }

  object AbstractState {

    def singleton(p: Path, a: A) = AbstractState(Some(Map(p -> a)))

    def read(p: Path) = singleton(p, allStat)

    def dir(p: Path) = singleton(p, Known(Set(AIsDir)))

    def file(p: Path) = singleton(p, Known(Set(AIsFile)))

    def create(p: Path, a: Stat) = AbstractState(Some(Map(p -> Known(Set(a)))))

    def write(p: Path) = singleton(p,  allStat)

    def rm(p: Path) = singleton(p, Known(Set(ADoesNotExist)))

    def exists(p: Path) = singleton(p, Known(Set(AIsFile, AIsDir)))

    def notDir(p: Path) = singleton(p, Known(Set(ADoesNotExist, AIsFile)))

    def notFile(p: Path) = singleton(p, Known(Set(ADoesNotExist, AIsDir)))

    val empty = AbstractState(Some(Map()))
    val error = AbstractState(None)

  }


  import AbstractState._

  def absEval(expr: Expr): AbstractState = expr match {
    case Mkdir(p) => create(p, AIsDir) + dir(p.getParent)
    case Error => error
    case Skip => empty
    case If(TestFileState(p, IsDir), e1, e2) => (dir(p) >> absEval(e1)) + (notDir(p) >> absEval(e2))
    case If(TestFileState(p, IsFile), e1, e2) => (file(p) >> absEval(e1)) + (notFile(p) >> absEval(e2))
    case If(TestFileState(p, DoesNotExist), e1, e2) => (rm(p) >> absEval(e1)) + (exists(p) >> absEval(e2))
    case If(a, e1, e2) => {
      val st = a.readSet.foldLeft(empty)((st, p) => st + read(p))
      (st >> absEval(e1)) + (st >> absEval(e2))
    }
    case Seq(e1, e2) => absEval(e1) >> absEval(e2)
    case CreateFile(p, _) => dir(p.getParent) + create(p, AIsFile)
    case Rm(p) => rm(p)
    case Cp(src, dst) => file(src) + dir(dst.getParent) + create(dst, AIsFile)
  }

  def absGraph[K](g: FSGraph[K]): AbstractState = {
    if (g.deps.isEmpty) {
      empty
    }
      else {
        val fringe = g.deps.nodes.filter(_.outDegree == 0).toList
        fringe.map(node => absEval(g.exprs(node.value))).reduce(_ || _)
      }
  }

  def pruneablePaths[A](graph: FSGraph[A]): Set[Path] = {
    val absStates = graph.exprs.mapValues(absEval)
    val combinedAbsState = absStates.values.reduce(_ || _)
    require(combinedAbsState.map.isDefined, "static error here--wow")
    combinedAbsState.map.get.toList
      .filter({
        case (_, Known(r)) => r.size == 1 && r.head == AIsFile
        case (_, ABot) => false
      })
      .map({ case (p, _) => p })
      .toSet
  }

  def prunePred(toPrune: Set[Path], pred: Pred): Pred = pred match {
    case True => True
    case False => False
    case Flip => Flip
    case And(a, b) => prunePred(toPrune, a) && prunePred(toPrune, b)
    case Or(a, b) => prunePred(toPrune, a) || prunePred(toPrune, b)
    case Not(a) => Not(prunePred(toPrune, a))
    case TestFileState(p, s) => {
      if (toPrune.contains(p)) {
        Flip
      }
      else {
        pred
      }
    }
    case ITE(_, _, _) => throw Unexpected("ITE")
  }

  def assertDir(p: Path) = If(TestFileState(p, IsDir), Skip, Error)

  def mayAssertParent(toPrune: Set[Path], p: Path) = {
    if (toPrune.contains(p.getParent)) Skip else assertDir(p.getParent)
  }

  def mkIf(a: Pred, e1: Expr, e2: Expr) = {
    if (e1 == e2) e1 else If(a, e1, e2)
  }

  def pruneExpr(toPrune: Set[Path], expr: Expr): Expr = expr match {
    case Mkdir(p) => {
      if (toPrune.contains(p)) {
        if (toPrune.contains(p.getParent)) Skip else assertDir(p.getParent)
      }
      else {
        expr
      }
    }
    case Error => Error
    case Skip => Skip
    case If(pred, e1, e2) => mkIf(pred,
                                pruneExpr(toPrune, e1),
                                pruneExpr(toPrune, e2))
    case Seq(e1, e2) => pruneExpr(toPrune, e1) >> pruneExpr(toPrune, e2)
    case CreateFile(p, _) => {
      if (toPrune.contains(p)) {
        if (toPrune.contains(p.getParent)) Skip else assertDir(p.getParent)
      }
      else {
        expr
      }
    }
    case Rm(p) =>  if (toPrune.contains(p)) Skip else expr
    case Cp(src, dst) => (toPrune.contains(src), toPrune.contains(dst)) match {
      case (false, false) => expr
      // Since src is read-only and dst is not, we can simply leave cp as-is
      case (true, false) => expr
      case (true, true) => {
        mayAssertParent(toPrune, src) >> mayAssertParent(toPrune, dst)
      }
      case (false, true) => {
        If(TestFileState(src, IsFile), mayAssertParent(toPrune, dst), Error)
      }
    }
  }

  def pruneGraph[A](graph: FSGraph[A]): FSGraph[A] = {
    val toPrune = pruneablePaths(graph)
    logger.info(s"Pruning: $toPrune")
    //val toPrune = toPrune_.filterNot(p => toPrune_.exists(p_ => p_ != p && p_.startsWith(p)))
    logger.info(s"Pruning removes ${toPrune.size} paths")
    FSGraph(graph.exprs.mapValues(e => pruneExpr(toPrune, e)),
            graph.deps)
  }

}


object DeterminismPruning {

  import rehearsal.PuppetSyntax.FSGraph
  import java.nio.file.Path
  import FSSyntax._
  import Implicits._

  def mergeMaps[A, B](lst: TraversableOnce[Map[A, B]]): Map[A, List[B]] = {
    def join(acc: Map[A, List[B]], m: Map[A, B]): Map[A, List[B]] = {
      m.foldLeft(acc) { case (acc, (k, v)) =>
        acc.get(k) match {
          case None => acc + (k -> List(v))
          case Some(vs) => acc + (k -> (v :: vs))
        }
      }
    }
    lst.foldLeft(Map[A, List[B]]())(join)
  }

  sealed trait A {
    def join(other: A): A = (this, other) match {
      case (ABot, x) => x
      case (x, ABot) => x
      case (ARead, ARead) => ARead
      case (ADir, ADir) => ADir
      case _ => AWrite
    }
  }

  case object AWrite extends A
  case object ADir extends A
  case object ARead extends A
  case object ABot extends A

  type AS = Map[Path, A]

  val empty = Map.empty[Path, A]

  def dir(st: AS, p: Path): AS = st + (p -> ADir)

  def read(st: AS, p: Path): AS = st + (p -> st.getOrElse(p, ABot).join(ARead))

  def write(st: AS, p: Path): AS = st + (p -> AWrite)

  def writes(st: AS): Set[Path] = st.filter({ case (p, v) => v == AWrite }).keySet

  def dirs(st: AS): Set[Path] = st.filter({ case (p, v) => v == ADir }).keySet

  def reads(st: AS): Set[Path] = st.filter({ case (p, v) => v == ARead }).keySet

  def join(st1: AS, st2: AS): AS = {
    (for (k <- (st1.keySet ++ st2.keySet).toList) yield {
      (k, st1.getOrElse(k, ABot).join(st2.getOrElse(k, ABot)))
    }).toMap
  }

  def joins(lst: TraversableOnce[AS]): AS = lst.foldLeft(empty)(join)

  def absEvalExpr(st: AS, expr: Expr): AS = expr match {
    case Mkdir(p) => {
      require(p.getParent() != null)
      dir(read(st, p.getParent), p)
    }
    case Error => st
    case Skip => st
    case If(TestFileState(p, IsDir), e1, e2) => {
      join(absEvalExpr(dir(st, p), e1), absEvalExpr(read(st, p), e2))
    }
    case If(a, e1, e2) => {
      val st_ = a.readSet.foldLeft(st)(read)
      join(absEvalExpr(st_, e1), absEvalExpr(st_, e2))
    }
    case Seq(e1, e2) => absEvalExpr(absEvalExpr(st, e1), e2)
    case CreateFile(p, _) => write(read(st, p.getParent()), p)
    case Rm(p) => write(read(st, p.getParent()), p)
    case Cp(src, dst) => write(read(read(st, src.getParent()), dst.getParent()), dst)
  }

  def absEval(expr: Expr): AS = absEvalExpr(Map.empty, expr)

  def pruneExpr(candidates: Set[Path], finalSt: AS, st: AS, expr: Expr): (AS, Expr) = {

    val indepSt = absEval(expr)
    val endSt = join(st, finalSt)
    //println(s"expr: $expr\nFinalSt: $finalSt\nst: $st\nindepSt: $indepSt")

    println("*************")
    println(expr)
    println(s"expression summary: $indepSt")
    println(s"context summary: $endSt")

    if (writes(indepSt).subsetOf(candidates) &&
        writes(indepSt).intersect(writes(endSt)).isEmpty &&
        dirs(indepSt).isEmpty &&
        reads(indepSt).intersect(writes(endSt)).isEmpty) {

      //      println("********")
//      println(writes(finalSt))
//      println(expr.fileSets.reads)
//      println(expr.fileSets.reads.intersect(dirs(st)))
//      println(expr.fileSets.reads.intersect(dirs(finalSt)))
      // TODO: Need to check what is written at end of program too
      println(s"Pruned $expr")
      (st, Skip)
    }
    else {
      expr match {
        case Mkdir(p) => (dir(read(st, p.getParent), p), expr)
        case Error => (st, Error)
        case Skip => (st, Skip)
        case If(TestFileState(p, IsDir), e1, e2) => {

          val (st1, e1_) = pruneExpr(candidates, finalSt, dir(st, p), e1)
          val (st2, e2_) = pruneExpr(candidates, finalSt, read(st, p), e2)

          (join(st1, st2), If(TestFileState(p, IsDir), e1_, e2_))
        }

        case If(a, e1, e2) => {
          val st_ = a.readSet.foldLeft(st)(read)
          val (st1, e1_) = pruneExpr(candidates, finalSt, st_, e1)
          val (st2, e2_) = pruneExpr(candidates, finalSt, st_, e2)
          (join(st1, st2), If(a, e1_, e2_))
        }
        case Seq(e1, e2) => {
          val (st1, e1_)  = pruneExpr(candidates, finalSt, st, e1)
          val (st2, e2_) =  pruneExpr(candidates, finalSt, st1, e2)
          (st2, Seq(e1_, e2_))
        }
        case CreateFile(p, c) => {
          (write(read(st, p.getParent()), p), expr)
        }
        case Rm(p) => {
          (write(read(st, p.getParent()), p), expr)
        }
        case Cp(src, dst) => {
          (write(read(read(st, src.getParent()), dst.getParent()), dst), expr)
        }
      }
    }
  }

  // Returns a set of paths, where each path is written to by only one resource
  // and not read by any other resources.
  def pruningCandidates[K](g: FSGraph[K]): Set[Path] = {
    def unobservableWrite(lst: List[A]): Boolean = {
      lst.filter(_ == AWrite).length == 1 &&
      lst.filter(_ == ARead).isEmpty &&
      lst.filter(_ == ADir).isEmpty
    }
    val absStates = g.exprs.values.map(e => absEvalExpr(Map.empty, e))
    val pathStates = mergeMaps(absStates)

    pathStates.toList
      .filter({ case (_, s) => unobservableWrite(s) })
      .map({ case (p, _) => p })
      .toSet
  }

  // Maps each node K to the abstract state child; sibling,
  // child is the abstract state that summarizes the child nodes of K
  // (i.e., nodes that depend on K) and sibling is the abstract state
  // that summarizes the siblings of K.
  def summarizeGraph[K](rest: AS, g: FSGraph[K]): (AS, Map[K, AS]) = {
    if (g.deps.isEmpty) {
      (rest, Map())
    }
    else {
      val fringe = g.deps.nodes.filter(_.outDegree == 0).toList
      val sts = fringe.map(node => node.value -> absEval(g.exprs(node.value)))


      val st = join(joins(fringe.map(node => absEval(g.exprs(node.value)))), rest)
      val map = fringe.map(node => node.value -> (join(rest, joins(sts.filter({ case(k, _) => k != node.value}).map(_._2))))).toMap

      val (st_, map_) = summarizeGraph(st, FSGraph(g.exprs, g.deps -- fringe))
      (st_, map_ ++ map)
    }

  }


  def pruneGraph[K](g: FSGraph[K]): FSGraph[K] = {
    val candidates = pruningCandidates(g)
    println(s"Candidates: $candidates")
    val finalSt = g.exprs.values.map(absEval).reduce(join)
    val (_, finalSts) = summarizeGraph(Map.empty, g)

    val exprs = g.exprs.toList.map({ case (k, e) =>
      k -> pruneExpr(candidates, finalSts(k), Map.empty, e)._2
    })
    FSGraph(exprs.toMap, g.deps)
  }

}

