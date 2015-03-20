package fsmodel.ext

object Implicits {

  implicit class RichExpr(e1: Expr) {

    def +(e2: Expr) = (e1, e2) match {
      case (Error, _) => e2
      case (_, Error) => e1
      case _ if e1 == e2 => e1 
      case _ => Alt(e1, e2)
    }

    def *(e2: Expr) = (e1, e2) match {
      case (Error, _ ) => Error
      case (_, Error) => Error
      case (_, Skip) => e1
      case (Skip, _) => e2
      case _ => Concur(e1, e2)
    }

    def >>(e2: Expr) = (e1, e2) match {
      case (Skip, _) => e2
      case (_, Skip) => e1
      case (Error, _) => Error
      case (_, Error) => Error
      case _ => Seq(e1, e2)
    }

  }

}
