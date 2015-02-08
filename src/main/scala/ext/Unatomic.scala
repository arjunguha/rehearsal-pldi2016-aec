package fsmodel.ext

import fsmodel.core
import Implicits._

private[ext] object Unatomic {

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

}