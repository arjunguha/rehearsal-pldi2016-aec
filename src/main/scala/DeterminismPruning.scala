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
