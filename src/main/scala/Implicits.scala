package fsmodel

import  scala.language.implicitConversions
import java.nio.file.{Path, Paths}

object Implicits {

  implicit def stringToPath(str: String): Path = Paths.get(str)

}

