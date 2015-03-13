package fsmodel.optExt

import Implicits._

private[optExt] object Unatomic {

  def unatomic(expr: Expr): Expr = expr match {
    case Seq(list) => Seq(list.map(unatomic(_)))
    case Alt(set) => Alt(set.map(unatomic(_)))
    case Atomic(p) => unatomic(p)
    case Concur(_, _) => throw new IllegalArgumentException(s"unatomic($expr)")
    case Error|Skip|Mkdir(_)|Rm(_)|Cp(_,_)|CreateFile(_, _) => expr
    case Filter(_) => expr
  }

}