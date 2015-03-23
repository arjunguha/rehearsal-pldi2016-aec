package fsmodel.core

import  scala.language.implicitConversions
import java.nio.file.{Path, Paths}

object Implicits {

  implicit def stringToPath(str: String): Path = Paths.get(str)

  implicit class RichString(str: String) {

    def toPath = Paths.get(str)
  }

  implicit def MapToPerfMap(map: Map[Path, FileState]): PerfMap[Path, FileState] = {
    PerfMap(map)
  }
}
