package eval

object Implicits {

  import  scala.language.implicitConversions
  import java.nio.file.{Path, Paths}

  implicit def stringToPath(str: String): Path = Paths.get(str)

  implicit class RichString(str: String) {

    def toPath = Paths.get(str)
  }

  implicit def MapToPerfMap(map: Map[Path, FileState]): PerfMap[Path, FileState] = {
    PerfMap(map)
  }

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
