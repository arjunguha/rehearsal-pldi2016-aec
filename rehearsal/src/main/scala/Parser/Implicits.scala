package parser

object Implicits {

  import Syntax._

  implicit class RichManifest(m: Manifest) {

    def >>(other: Manifest) = (m, other) match {
      case (Empty, _) => other
      case (_, Empty) => m
      case _ => Block(m, other)
    }
  }

}