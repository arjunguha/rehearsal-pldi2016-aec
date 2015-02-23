package fsmodel.ext

object Implicits {

  implicit class RichExpr(expr: Expr) {

    def +(other: Expr) = Alt(expr, other)
    def *(other: Expr) = Concur(expr, other)
    def >>(other: Expr) = Seq(expr, other)

  }

}