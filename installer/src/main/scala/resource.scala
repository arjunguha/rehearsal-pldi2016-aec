package puppet.runtime.core

import puppet.util._

import java.nio.file.{Files, LinkOption, Paths, Path}
import java.io.FileWriter

object Provider {

  type Resource = Map[String, String]

  def apply(r: Resource): Provider = r("type") match {
    case "File" => File(r)
    case "Package" => PuppetPackage(r)
    case "User" => User(r)
    case "Notify" => Notify(r)
    case "Service" => Service(r)
    case "Group" => Group(r)
    case "Exec" => Exec(r)
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
                       

    // TODO: Ignoring ownership and permissions for now
    // TODO : Ignoring source attribute
    def realize() {

      if (content.isDefined && (source.isDefined || target.isDefined))
        throw new Exception("content is mutually exclusive with source and target attributes")

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
         * link: removelink, createfile and set content if present
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
      val cmd = "apt-cache policy %s".format(name)
      val (sts, out, err) = Cmd.exec(cmd)
      if (0 == sts) {
        // Parse output for a version and return
        pattern.findAllIn(out).matchData.map(_.group(1)).toList.head
      }
      else {
        throw new Exception(s"$cmd failed: $err")
      }
    }

    def realize() {
      val cmd = ensure match {
        case Some("present") | Some("installed") => "apt-get -y -q install %s".format(name)
        case Some("absent") => "apt-get -y -q remove %s".format(name)
        case Some("purged") => "apt-get -y -q remove --purge %s".format(name)
        case Some("held")   => throw new Exception("NYI package held")
        case Some("latest") => "apt-get -y -q install %s=%s".format(name, latest)
        case _ => throw new Exception("One or more required attribute is missing")
      }

      println(s"Executing: $cmd")
      val (sts, _, err) = Cmd.exec(cmd)
      if(sts != 0) throw new Exception(err)
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

    private def userExists(user: String): Boolean = {
      val (sts, _, _) = Cmd.exec(s"id -u $user")
      (sts == 0)
    }

    private def gidExists(gid: String): Boolean = {
      val (sts, _, _) = Cmd.exec(s"getent group $gid")
      (sts == 0)
    }

    def realize() {

      // Hackish but puppet port, make sure shell binary exists and its executable
      if (shell.isDefined) {
        val p = shell.get
        if (!Files.exists(Paths.get(p)) || Files.isExecutable(Paths.get(p))) {
          throw new Exception(s"Invalid shell $p for user $name")
        }
      }

      if(gid.isDefined && !gidExists(gid.get)) {
        throw new Exception(s"Invalid gid $gid for user $name")
      }

      /* Linux add user to the same group as its username unless gid
       * attribute is specified
       * If no gid is specifed to useradd and a group by the name of
       * user exists then useradd returns error
       */
      val isDuplicate = userExists(name)
      val _gid = if(gid.isDefined) gid // If gid explicitly specified in manifest then 
                 else if(gidExists(name)) Some(name)
                 else None

      val cmd = (ensure, isDuplicate) match {
        case (Some("present"), true)  => None // TODO: Should we check all other params if they match
        case (Some("present"), false) => Some(List("useradd",
                                           _gid.map("-g %s".format(_)) getOrElse "",
                                           groups.map("-G %s".format(_)) getOrElse "",
                                           shell.map("-s %s".format(_)) getOrElse "",
                                           uid.map((u) => "-u %s".format(u.toString)) getOrElse "",
                                           home.map("-d %s".format(_)) getOrElse "",
                                           if(allowdupe) "-o" else "",
                                           if(managehome) "-m" else "",
                                           if(system) "-r" else "",
                                           name))

        // See if userdel is idempotent when user by the given name does not exist
        case (Some("absent"), true) => Some(List("userdel",
                                         if(managehome) "-r" else "",
                                         name))
        case (Some("absent"), false) => None

        case (Some("role"), _) => throw new Exception("role management in user not yet supported")

        case (_, _) => throw new Exception("Unknown 'ensure' value for user")
      }

      if(cmd.isDefined) {
        println(s"Executing: ${cmd.get mkString " "}")
        val (sts, _, err) = Cmd.exec(cmd.get mkString " ")
        if(sts != 0) { throw new Exception(err) }
      }
    }
  }

  case class Notify(res: Resource) extends Provider(res) {

    private val msg = r.get("message") getOrElse name

    def realize() { println(msg) }
  }

  case class Service(res: Resource) extends Provider(res) {
    private val validEnsureVals = Map("stopped"->"stopped", "false"->"stopped",
                                      "running"->"running", "true"->"running",
                                      ""-> "undef")
    private val validBoolVal = Map("true"->true, "false"->false)
    private val validEnableVals = validBoolVal
    private val validHasRestartVals = validBoolVal
    private val validHasStatusVals = validBoolVal
     
    val ensure = validVal("ensure", validEnsureVals) getOrElse (throw new Exception(s"Service $name 'ensure' attribute missing"))
    val binary = r.get("binary") getOrElse name
    val enable = validVal("enable", validEnableVals) getOrElse false // Whether a service should be enabled at boot time.
    val flags  = r.get("flags") getOrElse ""
    val hasrestart = validVal("hasrestart", validHasRestartVals) getOrElse false
    // if a service's init script has a functional status command,
    val hasstatus = validVal("hasstatus", validHasStatusVals) getOrElse true
    val path = r.get("path")
    /* pattern to search for in process table, used for stopping services that do not support init scripts
     * Also used for determining service status on those service whose init scripts do not include a status command
     */
    val pattern = r.get("pattern") getOrElse binary
    val restart = r.get("restart") // If not provided then service will be first stopped and then started
    val start = r.get("start") getOrElse "start"
    val stop = r.get("stop") getOrElse "stop"
    val status = r.get("status")

    // TODO : handle Refresh
    def realize() {

      // XXX: Since we are not supporting notifications, we do not need to deal with restart related stuff

      // Make sure binary exists after adding path variable to environment

      /* TODO : Mark service to start on reboot if enable */
      val (cmd, mode) = ensure match {
        case "stopped" => (Some(List("start", flags, binary)), "start")
        case "running" => (Some(List("stop", flags, binary)), "stop")
        case "undef" => (None, "") // TODO: should check if service running or not
        case _ => throw new Exception(s"Invalid value $ensure for a service provider")
      }

      if(cmd.isDefined) {
        puppet.installer.Services.enlist(binary, path getOrElse "", flags, mode)
        println(s"Executing: ${cmd.get mkString " "}")
        val (sts, _, err) = Cmd.exec(cmd.get mkString " ")
        if (sts != 0 ) throw new Exception(err)
      }
    }
  }

  case class Group(res: Resource) extends Provider(res) {
    private val validEnsureVals = List("present", "absent")
    private val validBoolVals = Map("true" -> true, "false" -> false, "yes" -> true, "no" -> false)
    private val validAllowDupeVals = validBoolVals
    private val validAttributeMembershipVals = List("inclusive","minimum")
    private val validSystemVals = validBoolVals

    val ensure = validVal("ensure", validEnsureVals) getOrElse (throw new Exception(s"Group $name 'ensure' attribute missing"))
    val allowdupe = validVal("allowdupe", validAllowDupeVals) getOrElse false
    val attribute_membership = validVal("attribute_membership", validAttributeMembershipVals)
    val gid = r.get("gid").map(_.toInt)
    private val isgidvalid = if(!gid.isDefined || gid.get >= 0) true else false
    val system = validVal("system", validSystemVals) getOrElse false

    def realize() {

      if (!isgidvalid)
        throw new Exception(s"Invalid gid: ${gid}")

      val cmd = ensure match {
        case "present" => List("groupadd",
                               "-f", // return success code even if group is already present
                               gid.map("-g %s".format(_)) getOrElse "",
                               if(allowdupe == true) "-o" else "",
                               name)
        case "absent" => List("groupdel", name)
        case _ => throw new Exception(s"Invalid ensure value: $ensure")
      }

      println(s"Executing: ${cmd mkString " "}")
      val (sts, _, err) = Cmd.exec(cmd mkString " ")
      if(sts != 0) throw new Exception(err)
    }
  }

  case class Exec(res: Resource) extends Provider(res) {

    val command = r.get("command") getOrElse name
    val path = r.get("path")
    val cwd = r.get("cwd")
    // TODO: This should have been an array
    val environment = r.get("environment")
    val creates = r.get("creates")
    val onlyif = r.get("onlyif")
    val unless = r.get("unless")
    val refresh = r.get("refresh")
    val refreshonly = r.get("refreshonly")
    // TODO : Sanity checks on integers to check if they are above 0
    val returns = r.get("returns").map(_.toInt) getOrElse 0 // Error is returned if executed command has any other return code
    val timeout = r.get("timeout").map(_.toInt) getOrElse 300 // This is in seconds, default value is from puppet code
    val tries = r.get("tries").map(_.toInt) getOrElse 1
    val try_sleep = r.get("try_sleep").map(_.toInt) getOrElse 0 // The number of seconds to sleep between command execution upon retry
    val group = r.get("group")
    val umask = r.get("umask")
    val user = r.get("user") // $HOME environment variable is not set when user attribute is specified

    // envvar is of the form var=value
    private def toEnvVar(envvar: String): (String, String) = {
      val arr = envvar split '='
      if (arr.length == 2) (arr(0), arr(1))
      else throw new Exception(s"Invalid environment variable: $envvar")
    }

    private def fileExists(file: String): Boolean = {
      val p = Paths.get(file)
      if (p.isAbsolute) Files.exists(p)
      else Files.exists(Paths.get((cwd getOrElse "") + "/" + file))
    }

    private def setPath(paths: String) =
      (paths split ':') foreach (ENV_PATH.append _)

    // TODO : Handle refresh
    def realize() {

      if (cwd.isDefined && !Files.isDirectory(Paths.get(cwd.get)))
        throw new Exception(s"cwd: ${cwd.get} is not a directory")

      // Set Environment path variable
      path.map(setPath _)

      // Get Command to Execute
      val cmd = command 

      // TODO : when environment is an array, call this function on each element
      val execenv = environment.map((e) => Seq((toEnvVar(e)))) getOrElse Seq()

      // determine if execute or not
      val should_exec = 
        (creates.isDefined && !this.fileExists(creates.get)) ||
        (onlyif.isDefined && Cmd.exec(onlyif.get)._1 == 0) ||
        (unless.isDefined && Cmd.exec(unless.get)._1 != 0) ||
        (!creates.isDefined && !onlyif.isDefined && !unless.isDefined)

      // for 'tries' execute and then sleep for time-out if failed
      def trycommand(tries_left: Int = tries,
                     cmd: String = cmd,
                     ocwd: Option[String] = cwd,
                     retval: Int = returns,
                     interval: Int = try_sleep*1000,
                     env: Seq[(String, String)] = execenv): Option[Int] = (tries_left, ocwd) match {
        case (0, _) => None // num tries got over, return
        case (_, Some(cwd)) if (Cmd.exec(cmd, cwd, env:_*)._1 == retval) => Some(0)
        case (_, None)      if (Cmd.exec(cmd, env:_*)     ._1 == retval) => Some(0)
        case (_, _) => Thread sleep interval; trycommand(tries_left-1)
      }

      if (should_exec) {
        println(s"Executing: $cmd")
        // trycommand(tries) getOrElse (throw new Exception(s"$cmd exec failed"))
        val (sts, out, err) = Cmd.exec(cmd)
        println(out)
        if (sts != 0) {
          System.err.println(err)
          throw new Exception(s"$cmd exec failed")
        }
      }
    }
  }
}
