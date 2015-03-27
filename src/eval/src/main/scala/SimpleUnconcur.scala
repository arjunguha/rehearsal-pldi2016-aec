package eval

import Implicits._

private[eval] object SimpleUnconcur {

  def unconcur(expr: Expr): Expr = expr match {
    case Atomic(p) => Atomic(unconcur(p))
    case Concur(Skip, q) => unconcur(q)
    case Concur(Error, _) => Error
    case Concur(Filter(a), q) => {
      // TODO(arjun): This assumes that all predicates are atomic.
      val e2 = unconcur(q)
      (Filter(a) >> e2) + (e2 >> Filter(a))
    }
    case Concur(If(a, p, q), r) => {
      (unconcur(r) >> If(a, unconcur(p), unconcur(q))) +
      (If(a, unconcur(p * r), unconcur(q * r)))
    }
    case Concur(Seq(p, q), r) => unconcur((p * r) >> q) + unconcur(p >> (q * r))
    case Concur(Alt(p, q), r) => unconcur(p * r) + unconcur(q * r)
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
    case If(a, p, q) => If(a, unconcur(p), unconcur(q))
    case Seq(p, q) => unconcur(p) >> unconcur(q)
    case Alt(p, q) => unconcur(p) + unconcur(q)
    case Error | Skip | Mkdir(_) | CreateFile(_, _) | Rm(_) | Cp(_, _) => expr
    case Filter(_) => {
      // TODO(arjun): This assumes that all predicates are atomic.
      expr
    }
  }

}
