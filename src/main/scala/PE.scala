package rehearsal

object PE {


  import FSSyntax._
  import java.nio.file.Path

  type State = Map[Path, FileState]

  def pePred(st: State, pred: Pred): Pred = pred match {
    case True => True
    case False => False
    case And(a, b) => pePred(st, a) && pePred(st, b)
    case Or(a, b) => pePred(st, a) || pePred(st, b)
    case Not(a) => !pePred(st, a)
    case TestFileState(p, s) => {
      st.get(p) match {
        case None => pred
        case Some(s_) => {
          if (s == s_) True else False
        }
      }
    }
  }

  def peExpr(st: State, expr: Expr): Option[(Expr, State)] = expr match {
    case Error => None
    case Skip => Some((Skip, st))
    case Mkdir(p) => (st.get(p.getParent), st.get(p)) match {
      case (Some(IsDir), Some(DoesNotExist)) => {
        Some((expr, st + (p.getParent -> IsDir) + (p -> IsDir)))
      }
      case (Some(_), Some(_)) => None
      case _ =>  Some((expr, st + (p.getParent -> IsDir) + (p -> IsDir)))
     }
     case CreateFile(p, h) => (st.get(p.getParent), st.get(p)) match {
       case (Some(IsDir), Some(DoesNotExist)) => {
         Some((expr, st + (p.getParent -> IsDir) + (p -> IsFile)))
       }
       case (Some(_), Some(_)) => None
       case _ => Some((expr, st + (p.getParent -> IsDir) + (p -> IsFile)))
     }
    case Cp(src, dst) => {
      // expr could be simplified more
      Some((expr, st + (src -> IsFile) + (dst -> IsFile) +
                  (src.getParent -> IsDir) + (dst.getParent -> IsDir)))
    }
    case Rm(p) => {
      // expr could be simplified more
      Some((expr, st + (p.getParent -> IsDir) + (p -> DoesNotExist)))
    }
    case Seq(e1, e2) =>  peExpr(st, e1) match {
      case None => None
      case Some((e1_, st1)) => peExpr(st1, e2) match {
        case None => None
        case Some((e2_, st2)) => Some((e1_ >> e2_, st2))
      }
    }
    case If(TestFileState(p, IsDir), Skip, Mkdir(p_)) if p == p_ => {
      Some((expr, st + (p -> IsDir) + (p.getParent -> IsDir)))
    }
    case If(a, e1, e2) => pePred(st, a) match {
      case True => peExpr(st, e1)
      case False => peExpr(st, e1)
      case a_ => (peExpr(Map(), e1), peExpr(Map(), e2)) match {
        case (Some((e1_, st1)), Some((e2_, st2))) => {
          val stCombined = st1.filterKeys(p => st1.get(p) == st2.get(p))
          Some((ite(a_, e1_, e2_), stCombined))
        }
        case (None, Some((e2_, _))) => Some((ite(a_, Error, e2_)), Map())
        case (Some((e1_, _)), None) => Some((ite(a_, e1_, Error)), Map())
        case (None, None) => None
      }
    }
  }

  def pe(e: Expr): Expr = peExpr(Map(), e) match {
    case None => Error
    case Some((e_, _)) => e_
  }


}
