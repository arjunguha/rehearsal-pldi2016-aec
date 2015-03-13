package fsmodel.optExt

import fsmodel.core
import Implicits._

private[optExt] object ToCore {

  def toCore(expr: Expr): core.Expr = expr match {
    case Error => core.Error
    case Skip => core.Skip
    case Filter(a) => core.If(a, core.Skip, core.Error)
    case Seq(Nil) => core.Skip
    case Seq(p :: Nil) => toCore(p)
    // Maybe better to split list in half
    case Seq(p :: ps) => core.Block(toCore(p), toCore(Seq(ps)))
    case Alt(set) => altHelper(set.toList)
    case Mkdir(path) => core.Mkdir(path)
    case CreateFile(path, hash) => core.CreateFile(path, hash)
    case Rm(path) => core.Rm(path)
    case Cp(src, dst) => core.Cp(src, dst)
    case Atomic(_) =>
      throw new IllegalArgumentException(s"toCore($expr)")
    case Concur(_, _) =>
      throw new IllegalArgumentException(s"toCore($expr)")
  }

  def altHelper(list: List[Expr]): core.Expr = list match {
    case Nil => core.Error
    case p :: Nil => toCore(p)
    case p :: ps => core.Alt(toCore(p), altHelper(ps))
  }

}
