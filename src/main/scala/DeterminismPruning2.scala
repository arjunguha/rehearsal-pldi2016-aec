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

//  object Lattice {
//
//    private[Lattice] val all = Set[FileState](IsFile, IsDir, DoesNotExist)
//
//    sealed trait V {
//
//      def +(other: V): V = (this, other) match {
//        case (Bot, y) => y
//        case (x, Bot) => x
//        case (Top, _) => Top
//        case (_, Top) => Top
//        case (Is(x), Is(y)) => Is(x union y)
//      }
//
//      def <=(other: V) = (this, other) match {
//        case (Bot, Bot) => true
//        case (Top, Top) => true
//        case (Is(x), Is(y)) => x.subsetOf(y)
//        case (Bot, _) => true
//        case (_, Top) => false
//      }
//
//      def unary_!(): V = this match {
//        case Bot => Bot
//        case Top => Top
//        case Is(set) => Is(all diff set)
//      }
//
//    }
//
//    case class Is(alts: Set[FileState]) extends V
//    case object Top extends V
//    case object Bot extends V
//
//    class St private[Lattice](map: Map[Path, V]) {
//
//      def apply(p: Path): V = map.get(p) match {
//        case None => Bot
//        case Some(v) => v
//      }
//
//      def ++(other: St): St = new St(map.combine(other.map) {
//        case (None, Some(y)) => Some(Bot + y)
//        case (Some(x), None) => Some(x + Bot)
//        case (Some(x), Some(y)) => Some(x + y)
//        case (None, None) => throw Unexpected("impossible case")
//      })
//
//      def +(pv: (Path, V)): St = {
////        val (p, newV) = pv
////        val oldV = this(p)
////        assert(oldV <= newV, "Not ascending")
//        new St(map + pv)
//      }
//
//      def unary_!(): St = new St(map.mapValues(v => !v))
//
//    }
//
//    val bot = new St(Map())
//
//  }
//
//  import Lattice._
//
//  def evalPred(st: St, pred: Pred): St = pred match {
//    case TestFileState(p, stat) => {
//      if (st(p) <= Is(Set(stat))) {
//        st + (p -> Is(Set(stat)))
//      }
//      else {
//        st + (p -> Top)
//      }
//    }
//    case True => st
//    case False => ??? // shouldn't be produced
//    case And(pred1, pred2) => evalPred(evalPred(st, pred1), pred2)
//    case Or(pred1, pred2) => evalPred(st, pred1) ++ evalPred(st, pred2)
//    case Not(p) => !evalPred(st, p)
//  }
//
//  def eval(st: St, expr: Expr): St = expr match {
//    case Error => st
//    case Skip => st
//    case If(pred, e1, e2) => {
//      val st_ = evalPred(st, pred)
//      eval(st_, e1) ++ eval(!st_, e2)
//    }
//    case Seq(e1, e2) => eval(eval(st, e1), e2)
//    case Mkdir(p) => st + (p -> Is(Set(IsDir)))
//    case CreateFile(p, _) => st + (p -> Is(Set(IsFile)))
//    case
//    case object Error extends Expr
//    case object Skip extends Expr
//    case class If private[FSSyntax] (a: Pred, p: Expr, q: Expr) extends Expr
//    case class Seq private[FSSyntax] (p: Expr, q: Expr) extends Expr
//    case class Mkdir private[FSSyntax] (path: Path) extends Expr
//    case class CreateFile private[FSSyntax] (path: Path, contents: String) extends Expr
//    case class Rm private[FSSyntax] (path: Path) extends Expr
//    case class Cp private[FSSyntax] (src: Path, dst: Path) extends Expr
//
//

}
