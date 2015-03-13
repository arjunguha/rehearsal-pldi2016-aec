package fsmodel.optExt

import fsmodel.optExt.Implicits._

private[optExt] object OptUnconcur {

  def unconcur(expr: Expr): Expr = expr match {
    case Atomic(p) => Atomic(unconcur(p))
    case Concur(Skip, q) => unconcur(q)
    case Concur(Error, _) => Error
    case Concur(Filter(a), q) => {
      // TODO(arjun): This assumes that all predicates are atomic.
      val e2 = unconcur(q)
      (Filter(a) >> e2) + (e2 >> Filter(a))
    }
    case Concur(Seq(Nil), r) => unconcur(r)
    case Concur(Seq(p :: Nil), r) => unconcur(Concur(p, r))
    case Concur(Seq(p :: ps), r) => {
      // NOTE(kgeffen) Cover one side each recursion instead of covering each
      // case twice (p1 * r >> p2 and p1 >> p2 * r share p1 >> r >> p2)
      // On last recursion, second side is covered since
      // case Con(Seq(p :: Nil), r) calls unc(Concur(p, r)) which has 2 terms
      val r_unc = unconcur(r)
      val p_unc = unconcur(p)
      val first = r_unc >> p_unc >> unconcur(Seq(ps))
      val rest = p_unc >> unconcur(Concur(Seq(ps), r_unc))
      first + rest
    }
    case Concur(Alt(set), r) => {
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
    // TODO(kgeffen) Optimize for when error is a part of sequence
    case Seq(list) => Seq(list.map(unconcur(_)))
    case Alt(set) => Alt(set.map(unconcur(_)))
    case Error | Skip | Mkdir(_) | CreateFile(_, _) | Rm(_) | Cp(_, _) => expr
    case Filter(_) => {
      // TODO(arjun): This assumes that all predicates are atomic.
      expr
    }
  }

}