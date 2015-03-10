package fsmodel.optExt

object Implicits {

  implicit class RichExpr(expr: Expr) {

    def +(other: Expr) = Alt(Set(expr, other))
    def *(other: Expr) = Concur(expr, other)
    def >>(other: Expr) = Seq(List(expr, other))

  }

}
