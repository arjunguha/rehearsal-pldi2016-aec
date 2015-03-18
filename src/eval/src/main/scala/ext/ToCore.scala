package fsmodel.ext

import fsmodel.core
import Implicits._

private[ext] object ToCore {

  def toCore(expr: Expr): core.Expr = expr match {
    case Error => core.Error
    case Skip => core.Skip
    case Filter(a) => core.If(a, core.Skip, core.Error)
    case If(a, p, q) => core.If(a, toCore(p), toCore(q))
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