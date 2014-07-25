package puppet.runtime.core

import puppet.util._

object Provider {

  type Resource = Map[String, String]

  def apply(r: Resource): Provider = r("type") match {
    case "File" => File(r)
    case "Package" => PuppetPackage(r)
    case "User" => User(r)
    case "Notify" => Notify(r)
    case _ => throw new Exception("Resource type \"%s\" not supported yet".format(r("type")))
  }

  sealed abstract class Provider (val r: Resource) {
    val name = r("name")
    def realize()

    protected def validVal[T](property: String, options: Map[String, T]): Option[T] = {
      r.get(property).map(options.get(_)).flatten
    }

    protected def validVal(property: String, options: List[String]): Option[String] = {
      validVal(property, options.zip(options).toMap)
    }
  }

  case class File(res: Map[String, String]) extends Provider(res) {
    private val validEnsureVals = List("present", "absent", "file", "directory", "link")
    private val validChksmVals = List("md5", "md5lite", "sha256", "sha256lite", "mtime", "ctime", "none")
    private val validBoolVals = Map("true"->true, "false"->false,
                                    "yes"->true, "no"->false)

    val path = r.get("path") getOrElse name
    val ensure = validVal("ensure", validEnsureVals)
    // val checksum = validVal("checksum", validChksmVals) getOrElse "md5"
    val force = validVal("force", validBoolVals) getOrElse false
    val purge = validVal("purge", validBoolVals) getOrElse false
    // val replace = validVal("replace", validBoolVals) getOrElse false
    val source = r.get("source")
    val target = r.get("target")
    val content = r.get("content")

    import java.nio.file.{Files, LinkOption, Paths, Path}
    import java.io.FileWriter

    private def ignore(path:String): String = path
    private def createfile(path: String): String = { Files.createFile(Paths.get(path)); path }
    private def writefile(content: String)(path: String): String = { (new FileWriter(path, false)).write(content); path }
    private def deletefile(path: String): String = { Files.deleteIfExists(Paths.get(path)); path }
    private def deletelink(path: String): String = deletefile(path)
    private def createlink(target: String)(path: String): String = { Files.createSymbolicLink(Paths.get(path), Paths.get(target)); path }
    private def createdir(path: String): String = { Files.createDirectory(Paths.get(path)); path }
    private def deletedir(path: String): String = {
      def recurdeletedir(p: Path) {
        if(Files.isDirectory(p, LinkOption.NOFOLLOW_LINKS))
          p.toFile.listFiles.foreach((f: java.io.File) => recurdeletedir(f.toPath))
        Files.deleteIfExists(p)
      }

      recurdeletedir(Paths.get(path))
      path
    }


    type Action = String=>String

    private def fileaction(path: String)
                          (missing: Action,
                           directory: Action,
                           regularfile: Action,
                           symlink: Action): String = {

      val nolinks = LinkOption.NOFOLLOW_LINKS
      Files.exists(Paths.get(path), nolinks) match {
        case false => missing(path)
        case true if Files.isDirectory   (Paths.get(path), nolinks) => directory(path)
        case true if Files.isRegularFile (Paths.get(path), nolinks) => regularfile(path)
        case true if Files.isSymbolicLink(Paths.get(path)) => symlink(path)
        case _ => throw new Exception("Not Anticipated")
      }
    }

    val action = fileaction(path) _
                       

    // TODO: Ignoring ownershp and permissions for now
    // TODO : Ignoring source attribute
    def realize() {

      if (content.isDefined && (source.isDefined || target.isDefined))
        throw new Exception("content is mutually exclusive with source and target")

      val createfilewithcontent: Action = content.map((c) => createfile _ andThen (writefile(c) _)) getOrElse createfile

      ensure match {
        // Broken symlinks are ignored
        /* What if content is set 
         *   - Depends on file type
         *     o For Links, content is ignored
         *     o For normal, content is applied
         *     o For directory, content is ignored
         */
        case Some("present") => action(createfilewithcontent,
                                       ignore,
                                       content.map((c) => writefile(c) _) getOrElse ignore,
                                       ignore)

        /*
         * Cases 
         * If already absent then don't do anything
         *  Directory: if force is set then remove otherwise ignore
         *  File: remove if present
         *  Symlink: Remove link (but not the target)
         */
        case Some("absent") => action(ignore,
                                      if(force) deletedir else ignore,
                                      deletefile,
                                      deletelink)

        /* missing: Create a file with content if content present
         * directory: if force is set then remove directory createFile and set content if present else ignore
         * file: if content set then set content else ignore
         * link: removelink, createfile and set content if preseet
         */
        case Some("file") => action(createfilewithcontent,
                                    (if(force) deletedir _ else ignore _) andThen createfilewithcontent,
                                    content.map((c) => writefile(c) _) getOrElse ignore,
                                    deletelink _ andThen createfilewithcontent)
          
        /* Missing: Create new directory
         * Directory: Ignore
         * File: remove file and create directory
         * link: remove link and create directory
         */
        /* TODO: Enables "source", "recurse", "recurselimit", "ignore", "purge" attributes */
        case Some("directory") => action(createdir,
                                         ignore,
                                         deletefile _ andThen createdir _,
                                         deletelink _ andThen createdir _)

        /*
         * Missing: create sym link with target
         * directory: if(force) removedir andThen createlink else ignore
         * file: delete file and create link
         * link: ignore
         */
        case Some("link") if target.isDefined => action(createlink(target.get),
                                                        if(force) deletedir _ andThen createlink(target.get) _ else ignore,
                                                        deletefile _ andThen createlink(target.get) _,
                                                        ignore)
         
        case _ => throw new Exception("One or more required attribute missing")
      }
    }
  }

  case class PuppetPackage(res: Resource) extends Provider(res) {

    private val validEnsureVals = List("present", "installed", "absent", "purged", "held", "latest")

    val ensure = validVal("ensure", validEnsureVals)

    def latest: String = {

      import scala.collection.JavaConversions
      import scala.util.matching.Regex._

      val pattern = """Candidate:\s+(\S+)\s""".r
      val output = Cmd.exec("apt-cache policy %s".format(name)).get
      // Parse output for a version and return
      pattern.findAllIn(output).matchData.map(_.group(1)).toList.head
    }

    def realize() {
      val cmd = ensure match {
        case Some("present") | Some("installed") => "apt-get -y -q install %s".format(name)
        case Some("absent") => "apt-get -y -q remove %s".format(name)
        case Some("purged") => "apt-get -y -q remove --purge %s".format(name)
        case Some("held")   => throw new Exception("NYI held")
        case Some("latest") => "apt-get -y -q install %s=%s".format(name, latest)
        case _ => throw new Exception("One or more required attribute is missing")
      }

      Cmd.exec(cmd).get
    }
  }

  case class User(res: Resource) extends Provider(res) {

    private val validEnsureVals = List("present", "absent", "role")
    private val validBoolVals = Map("true"->true, "false"->false,
                                    "yes"->true, "no"->false)

    import java.nio.file.{Files, LinkOption, Paths, Path}

    val ensure = validVal("ensure", validEnsureVals)
    val gid = r.get("gid")
    // Sanity check => if multiple then they should be comma separated without spaces, multiple groups should be specified as an array
    val groups = r.get("groups")

    val shell = r.get("shell")
    val uid = r.get("uid").map(_.toInt)
    // Directory must be created separately and is not checked for existence
    val home = r.get("home")

    val comment = r.get("comment")
    val expiry = r.get("expiry")

    val allowdupe = validVal("allowdupe", validBoolVals) getOrElse false
    val managehome = validVal("managehome", validBoolVals) getOrElse false
    val system = validVal("system", validBoolVals) getOrElse false

    def realize() {

      // Hackish but puppet port, make sure shell binary exists and its executable
      if (shell.isDefined) {
        val p = shell.get
        if (!Files.exists(Paths.get(p)) || Files.isExecutable(Paths.get(p))) {
          throw new Exception("Invalid shell for user")
        }
      }

      val cmd = ensure match {
        case Some("present") => List("useradd",
                                     gid.map("-g %s".format(_)) getOrElse "",
                                     groups.map("-G %s".format(_)) getOrElse "",
                                     shell.map("-s %s".format(_)) getOrElse "",
                                     uid.map((u) => "-u %s".format(u.toString)) getOrElse "",
                                     home.map("-d %s".format(_)) getOrElse "",
                                     if (allowdupe) "-o" else "",
                                     if (managehome) "-m" else "",
                                     if (system) "-r" else "",
                                     name)

        case Some("absent") => List("userdel",
                                    if (managehome) "-r" else "",
                                    name)

        case Some("role") => throw new Exception("role management in user not yet supported")

        case _ => throw new Exception("Unknown 'ensure' value for user")
      }

      Cmd.exec(cmd mkString " ").get
    }
  }

  case class Notify(res: Resource) extends Provider(res) {

    val msg = r.get("message") getOrElse name

    def realize() {
      println(msg)
    }
  }
}
