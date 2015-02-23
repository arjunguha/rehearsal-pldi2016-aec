package fsmodel.ext

import fsmodel.core
import fsmodel.optExt
import Implicits._

private[ext] object ToOpt {

  def toOpt(expr: Expr): optExt.Expr = expr match {
    case Error => optExt.Error
    case Skip => optExt.Skip
    case Filter(a) => optExt.Filter(a)
    case Seq(p, q) => (toOpt(p), toOpt(q)) match {
      case (optExt.Skip, q)       => q
      case (p, optExt.Skip)       => p
      case (optExt.Error, _)      => optExt.Error
      case (_, optExt.Error)      => optExt.Error
      case (optExt.Seq(lst1), optExt.Seq(lst2)) => optExt.Seq(lst1 ::: lst2)
      case (optExt.Seq(lst1), q)                => optExt.Seq(lst1 :+ q)
      case (p, optExt.Seq(lst2))                => optExt.Seq(p +: lst2)
      case (p, q)                               => optExt.Seq(p :: q :: Nil)
    }
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
