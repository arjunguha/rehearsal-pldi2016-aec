package puppet.runtime.core

import scala.sys.process._

object Provider {

  import puppet.core.eval._

  def apply(r: Resource): Provider = r.typ match {
    case "File" => File(r)
    case "Package" => PuppetPackage(r)
    case "User" => User(r)
    case _ => throw new Exception("Resource type \"%s\" not supported yet".format(r.typ))
  }

  sealed abstract class Provider (val r: Resource) {
    val name = r.name
    def realize: ProcessBuilder /* Is this the right type */

    import scala.language.implicitConversions

    protected implicit def valueToString(v: Value): String = v.toPString

    protected def validVal[T](property: String, options: List[T])
                             (implicit coerceT: Value => T): Option[T] = {
      r.params.get(property).map(coerceT(_)).find((p) => options.exists(p == _))
    }
  }

  case class File(res: Resource) extends Provider(res) {
    private val validEnsureVals = List("present", "absent", "file", "directory", "link")
    private val validChksmVals = List("md5", "md5lite", "sha256", "sha256lite", "mtime", "ctime", "none")
    private val validForceVals = Map("true"->true, "false"->false,
                                     "yes"->true, "no"->false)
    val path = r.params.get("path").map(_.toPString) getOrElse name
    val ensure = validVal("ensure", validEnsureVals)
    // val checksum = validVal("checksum", validChksmVals) getOrElse "md5"
    val force = validVal("force", validForceVals.keys.toList).map(validForceVals(_)) getOrElse false
    val purge = validVal("purge", validForceVals.keys.toList).map(validForceVals(_)) getOrElse false
    val replace = validVal("replace", validForceVals.keys.toList).map(validForceVals(_)) getOrElse false
    val source = r.params.get("source").map(_.toPString)
    val target = r.params.get("target").map(_.toPString)
    val content = r.params.get("content").map(_.toPString)

    def realize: ProcessBuilder = {
      if (content.isDefined && source.isDefined || target.isDefined)
        throw new Exception("content is mutually exclusive with source and target")

      // What is the current state of file?

      ensure match {
        case Some("present") => Process("ls")
        case Some("absent") => Process("ls")
        case Some("file") => Process ("ls")
        case Some("directory") => Process ("ls")
        case Some("link") => Process ("ls")
        case _ => throw new Exception("ensure field not defined")
      }
    }
  }

  case class PuppetPackage(res: Resource) extends Provider(res) {
    def realize: ProcessBuilder = Process("ls")
  }

  case class User(res: Resource)  extends Provider(res) {
    def realize: ProcessBuilder = Process("ls")
  }
}
