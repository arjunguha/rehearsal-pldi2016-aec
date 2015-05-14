package eval

object Implicits {

  import scala.language.implicitConversions
  import java.nio.file.{Path, Paths, Files}
  import scalax.collection.Graph
  import scalax.collection.edge.LDiEdge
  import scalax.collection.GraphEdge.DiEdge
  import java.security.MessageDigest

  implicit def stringToPath(str: String): Path = Paths.get(str)

  implicit def contentToHash(content: String): Array[Byte] =
    MessageDigest.getInstance("MD5").digest(content.getBytes)

  implicit class RichString(str: String) {

    def toPath = Paths.get(str)
  }

  implicit class RichPred(a: Pred) {

    def &&(b: Pred): Pred = (a, b) match {
      case (True, _) => b
      case (_, True) => a
      case _ => And(a, b)
    }

    def ||(b: Pred): Pred = (a, b) match {
      case (True, _) => True
      case (False, _) => b
      case (_, True) => True
      case (_, False) => a
      case _ => Or(a, b)
    }

    def unary_!(): Pred = a match {
      case Not(True) => False
      case Not(False) => True
      case Not(a) => a
      case _ => Not(a)
    }
  }

  implicit class RichExpr(e1: Expr) {

    def >>(e2: Expr) = (e1, e2) match {
      case (Skip, _) => e2
      case (_, Skip) => e1
      case (Error, _) => Error
      case (_, Error) => Error
      case _ => Seq(e1, e2)
    }
  }

}
