package rehearsal

case class ConfigError(message: String) extends RuntimeException(message)

object Settings {

  import rehearsal.Implicits._
  import config._
  import Config.Implicits._

  private val conf = {
    val prop = System.getProperty("rehearsal.conf")
    if (prop != null) {
      Config.fromFile(prop.toPath)
    }
    else {
      Config.fromFile("rehearsal.conf".toPath)
    }
  }

  val packageHost = conf.string("package-host")
    .getOrElse(throw ConfigError("package-host must be a string"))

  val assumedDirs = conf.stringList("assumed-directories")
    .getOrElse(throw ConfigError("assumed-directories must be a list of strings"))
    .map(_.toPath)
}
