package fsmodel.optExt

import fsmodel.core
import fsmodel.optExt.Implicits._

private[optExt] object SimpleUnconcur {

  def unconcur(expr: Expr): Expr = expr match {
    case Atomic(p) => Atomic(unconcur(p))
    case Concur(Skip, q) => unconcur(q)
    case Concur(Error, _) => Error
    case Concur(Filter(a), q) => {
      // TODO(arjun): This assumes that all predicates are atomic.
      val e2 = unconcur(q)
      (Filter(a) >> e2) + (e2 >> Filter(a))
    }
    case Concur(Seq(Nil), r) => {
      unconcur(r)
    }
    case Concur(Seq(p :: ps), r) => {
      unconcur((p * r) >> Seq(ps)) + unconcur(p >> (Concur(Seq(ps), r)))
    }
    case Concur(Alt(set), r) => {
      // TODO(kgeffen) We talked about not commiting to ordering too early.
      // Might be relevant here
      Alt(set.map(p => unconcur(Concur(p, r))))
    }
    case Concur(Concur(p, q), r) => unconcur(unconcur(p * q) * r)
    case Concur(Atomic(p), q) => {
      val e1 = Atomic(unconcur(p))
      val e2 = unconcur(q)
      (e1 >> e2) + (e2 >> e1)
    }
    case Concur(p @ (Mkdir(_)|Rm(_)|CreateFile(_,_)|Cp(_,_)), q) => {
      val e2 = unconcur(q)
      (p >> e2) + (e2 >> p)
    }
    case Seq(Nil) => Skip
    case Seq(p :: ps) => unconcur(p) >> unconcur(Seq(ps))
    case Alt(set) => Alt(set.map(unconcur(_)))
    case Error | Skip | Mkdir(_) | CreateFile(_, _) | Rm(_) | Cp(_, _) => expr
    case Filter(_) => {
      // TODO(arjun): This assumes that all predicates are atomic.
      expr
    }
  }

}
