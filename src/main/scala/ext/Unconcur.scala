package fsmodel.ext

import fsmodel.core

private[ext] object Unconcur {

  trait SmartConstructors {
    def alt(p: Expr, q: Expr): Expr
    def concur(p: Expr, q: Expr): Expr
    def seq(p: Expr, q: Expr): Expr
  }

  object NaiveConstructors extends SmartConstructors {
    def alt(p: Expr, q: Expr): Expr = Alt(p, q)
    def concur(p: Expr, q: Expr): Expr = Concur(p, q)
    def seq(p: Expr, q: Expr): Expr = Seq(p, q)
  }

  // TODO(arjun): Don't use Java-like names
  object CommutativityCheckingConstructors extends SmartConstructors {

    def alt(p: Expr, q: Expr): Expr = (p, q) match {
      // TODO(arjun): When applied recursively, this is a quadratic operation.
      // It will help if object-equality <=> pointer-equality.
      case (Seq(p1, p2), Seq(q1, q2))
        if (p1 == q2 && p2 == q1 && p1.commutesWith(p2)) => p
      case _ => Alt(p, q)
    }

    def concur(p: Expr, q: Expr): Expr = Concur(p, q)

    def seq(p: Expr, q: Expr): Expr = Seq(p, q)
  }

  class Make(constructors: SmartConstructors) {

    implicit class RichExpr(expr: Expr) {
      def +(other: Expr) = constructors.alt(expr, other)
      def *(other: Expr) = constructors.concur(expr, other)
      def >>(other: Expr) = constructors.seq(expr, other)
    }

    def unconcur(expr: Expr): Expr = expr match {
      case Atomic(p) => Atomic(unconcur(p))
      case Concur(Skip, q) => unconcur(q)
      case Concur(Error, _) => Error
      case Concur(Filter(a), q) => {
        // TODO(arjun): This assumes that all predicates are atomic.
        val e2 = unconcur(q)
        (Filter(a) >> e2) + (e2 >> Filter(a))
      }
      case Concur(Seq(p, q), r) => unconcur((p * r) >> q) + unconcur(p >> (q * r))
      case Concur(Alt(p, q), r) => unconcur(p * r) + unconcur(q * r)
      case Concur(Concur(p, q), r) => unconcur(unconcur(p * q) * r)
      case Concur(Atomic(p), q) => {
        val e1 = Atomic(unconcur(p))
        val e2 = unconcur(q)
        (e1 >> e2) + (e2 >> e1)
      }
      case Concur(Mkdir(path), q) => {
        val e2 = unconcur(q)
        (Mkdir(path) >> e2) + (e2 >> Mkdir(path))
      }
      case Concur(Rm(path), q) => {
        val e2 = unconcur(q)
        (Rm(path) >> e2) + (e2 >> Rm(path))
      }
      case Concur(CreateFile(path, hash), q) => {
        val e2 = unconcur(q)
        (CreateFile(path, hash) >> e2) + (e2 >> CreateFile(path, hash))
      }
      case Concur(Cp(src, dst), q) => {
        val e2 = unconcur(q)
        (Cp(src, dst) >> e2) + (e2 >> Cp(src, dst))
      }
      case Seq(p, q) => unconcur(p) >> unconcur(q)
      case Alt(p, q) => unconcur(p) + unconcur(q)
      case Error | Skip | Mkdir(_) | CreateFile(_, _) | Rm(_) | Cp(_, _) => expr
      case Filter(_) => {
        // TODO(arjun): This assumes that all predicates are atomic.
        expr
      }
    }
  }

  val Naive = new Make(NaiveConstructors)
  val Opt = new Make(CommutativityCheckingConstructors)

}