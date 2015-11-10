package rehearsal

class FSTable {

  import java.nio.file.Path
  import FSSyntax._
  import Implicits._


  type Action = Option[Map[Path, FileState]]


  implicit object ActionSemiRing extends SemiRing[Action] {
    val zero = None
    val one = Some(Map[Path, FileState]())
  }

  import ActionSemiRing._

  val dd = FSBDD[Action]

  import dd._

  def seq(d1: dd.Node, d2: dd.Node): dd.Node = (d1, d2) match {
    case (Leaf(None), _) => Leaf(None)
    case (_, Leaf(None)) => Leaf(None)
    case (Leaf(Some(m1)), Leaf(Some(m2))) => Leaf(Some(m1 ++ m2)) // right-biased
    case (Leaf(Some(m)), Branch(a2@TestFileState(p, s), lo, hi)) => {
      m.get(p) match {
        case Some(s_) => {
          if (s == s_) {
            seq(d1, hi)
          }
          else {
            seq(d1, lo)
          }
        }
        case None => {
          Branch(a2, seq(d1, lo), seq(d1, hi))
        }
      }
    }
    case (Branch(a1, lo1, hi1), _) => {
//      val lhs = seq(lo1, d2).restrict(a1, false)
//      val rhs = seq(hi1, d2).restrict(a1, true)
//      lhs.applyOp(rhs) {
//        case (None, None) => None
//        case (Some(m1), None) => Some(m1)
//        case (None, Some(m2)) => Some(m2)
//        case (Some(_), Some(_)) => throw Unexpected("expected disjoint in sequencing")
//      }
      Branch(a1, seq(lo1, d2), seq(hi1, d2))
    }
  }

  def mkddPred(pred: Pred): Node = pred match {
    case True => Leaf(ActionSemiRing.one)
    case False => Leaf(ActionSemiRing.zero)
    case And(pred1, pred2) => mkddPred(pred1).applyOp(mkddPred(pred2)) {
      case (Some(_), Some(_)) => ActionSemiRing.one
      case _ => ActionSemiRing.zero
    }
    case Or(pred1, pred2) => mkddPred(pred1).applyOp(mkddPred(pred2)) {
      case (Some(_), _) => ActionSemiRing.one
      case (_, Some(_)) => ActionSemiRing.one
      case _ => ActionSemiRing.zero
    }
    case Not(pred_) => mkddPred(pred_).applyOp(Leaf(ActionSemiRing.one)) {
      case (Some(_), _) => ActionSemiRing.zero
      case (None, _) => ActionSemiRing.one
    }
    case TestFileState(p, s) => Branch(TestFileState(p, s), Leaf(ActionSemiRing.zero), Leaf(ActionSemiRing.one))
    case ITE(_, _, _) => throw NotImplemented("ITE")
    case Flip  => throw NotImplemented("ITE")
  }

  def mkddExpr(expr: Expr): Node = expr match {
    case Error => Leaf(zero)
    case Skip => Leaf(one)
    case If(a, e1, e2) => {
      val aNode = mkddPred(a)
      seq(aNode, mkddExpr(e1)).applyOp(seq(mkddPred(Not(a)), mkddExpr(e2))) {
        case (None, None) => None
        case (Some(m1), None) => Some(m1)
        case (None, Some(m2)) => Some(m2)
        case (Some(m1), Some(m2)) => {
          throw Unexpected(s"expected leaves to be disjoint, got $m1 and $m2")
        }
      }
    }
    case Seq(e1, e2) => seq(mkddExpr(e1), mkddExpr(e2))
    case Mkdir(p) => Leaf(Some(Map(p -> IsDir)))
    case CreateFile(p, s) => Leaf(Some(Map(p -> IsFile)))
    case Rm(p) => Leaf(Some(Map(p -> DoesNotExist)))
    case Cp(_, _) => throw NotImplemented("CP")
  }



}