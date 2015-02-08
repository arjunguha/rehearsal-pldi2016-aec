package fsmodel.ext

import fsmodel.core

private[ext] object Compiler {

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

  def unatomic(expr: Expr): Expr = expr match {
    case Error => Error
    case Skip => Skip
    case Filter(a) => Filter(a)
    case Seq(p, q) => unatomic(p) >> unatomic(q)
    case Alt(p, q) => unatomic(p) + unatomic(q)
    case Mkdir(path) => Mkdir(path)
    case CreateFile(path, hash) => CreateFile(path, hash)
    case Rm(path) => Rm(path)
    case Cp(src, dst) => Cp(src, dst)
    case Atomic(p) => Atomic(unatomic(p))
    case Concur(_, _) =>
      throw new IllegalArgumentException(s"unatomic($expr)")
  }

  def toCore(expr: Expr): core.Expr = expr match {
    case Error => core.Error
    case Skip => core.Skip
    case Filter(a) => core.If(a, core.Skip, core.Error)
    case Seq(p, q) => core.Block(toCore(p), toCore(q))
    case Alt(p, q) => core.Alt(toCore(p), toCore(q))
    case Mkdir(path) => core.Mkdir(path)
    case CreateFile(path, hash) => core.CreateFile(path, hash)
    case Rm(path) => core.Rm(path)
    case Cp(src, dst) => core.Cp(src, dst)
    case Atomic(_) =>
      throw new IllegalArgumentException(s"toCore($expr)")
    case Concur(_, _) =>
      throw new IllegalArgumentException(s"toCore($expr)")
  }

}