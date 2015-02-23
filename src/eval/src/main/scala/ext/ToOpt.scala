package fsmodel.ext

import fsmodel.core
import fsmodel.optExt
import Implicits._

private[ext] object ToOpt {

  def toOpt(expr: Expr): optExt.Expr = expr match {
    case Error => optExt.Error
    case Skip => optExt.Skip
    case Filter(a) => optExt.Filter(a)
    case Seq(p, q) => optExt.Seq(List(toOpt(p), toOpt(q)))
    case Alt(p, q) => optExt.Alt(Set(toOpt(p), toOpt(q)))
    case Mkdir(path) => optExt.Mkdir(path)
    case CreateFile(path, hash) => optExt.CreateFile(path, hash)
    case Rm(path) => optExt.Rm(path)
    case Cp(src, dst) => optExt.Cp(src, dst)
    case Atomic(_) =>
      throw new IllegalArgumentException(s"toCore($expr)")
    case Concur(_, _) =>
      throw new IllegalArgumentException(s"toCore($expr)")
  }

}