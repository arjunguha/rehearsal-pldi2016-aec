package fsmodel.ext

import fsmodel.core
import Implicits._

private[ext] object Unatomic {

  def unatomic(expr: Expr): Expr = expr match {
    case Seq(p, q) => unatomic(p) >> unatomic(q)
    case Alt(p, q) => unatomic(p) + unatomic(q)
    case Atomic(p) => unatomic(p)
    case Concur(_, _) => throw new IllegalArgumentException(s"unatomic($expr)")
    case Error|Skip|Mkdir(_)|Rm(_)|Cp(_,_)|CreateFile(_, _) => expr
    case Filter(_) => expr
  }

}