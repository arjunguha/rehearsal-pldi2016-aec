package pipeline

import puppet.common.util._
import eval._
import eval.Implicits._

/*
 * Give filesystem semantics to resources
 *
 * Expresses resources in terms of file system changes
 */
private[pipeline] object ResourceToExpr {

  import java.nio.file.Path

  import puppet.common.resource._
  import puppet.common.resource.Extractor._

  val pkgcache = new PackageCache("/tmp/rehearsal/pkgs/")

  def Block(es: Expr*): Expr =
    es.foldRight(Skip: eval.Expr)((e, expr) => e >> expr)

  def Content(s: String): Array[Byte] = {
    import java.security.MessageDigest
    MessageDigest.getInstance("MD5").digest(s.getBytes)
  }


  val validBoolVals = List ((BoolV(true): Value, true),
                            (BoolV(false): Value, false),
                            (StringV("yes"): Value, true),
                            (StringV("no"): Value, false)).toMap

  def validVal[T](r: Resource, property: String,
                  options: Map[Value, T]): Option[T] = {
    r.getRawVal(property).map(options.get(_)).flatten
  }

  def validVal(r: Resource, property: String,
               options: List[String]): Option[String] = {
    val m = options.map((o) => (StringV(o): Value, o)).toMap
    validVal(r, property, m)
  }

  def File(r: Resource): Expr = {

    val validEnsureVals = List("present", "absent", "file", "directory", "link")

    val path = r.get[String]("path") getOrElse r.name
    val source = r.get[String]("source")
    val content = r.get[String]("content")
    val ensure = validVal(r, "ensure", validEnsureVals) orElse {
      if(content.isDefined) Some("present") else None
    }
    val force = validVal(r, "force", validBoolVals) getOrElse false
    val purge = validVal(r, "purge", validBoolVals) getOrElse false
    val target = r.get[String]("target")

    // TODO: Ignoring ownership and permissions for now
    // TODO : Ignoring source attribute
    val p = path
    val c = Content(content getOrElse "")
//     val t = target getOrElse "/tmp/"

    val _ensure = if (ensure.isDefined) ensure
                  else if (source.isDefined) Some("file")
                  else None

    _ensure match {
      // Broken symlinks are ignored
      /* What if content is set
       *   - Depends on file type
       *     o For Links, content is ignored
       *     o For normal, content is applied
       *     o For directory, content is ignored
       */
      case Some("present") => If(TestFileState(p, IsFile),
                                 Block(Rm(p), CreateFile(p, c)), // true branch
                                 If(TestFileState(p, DoesNotExist),
                                    CreateFile(p, c),
                                    Skip))

      /*
       * Cases
       * If already absent then don't do anything
       *  Directory: if force is set then remove otherwise ignore
       *  File: remove if present
       *  Symlink: Remove link (but not the target)
       */
      case Some("absent") if force => If(TestFileState(p, IsDir),
                                         Rm(p),
                                         If(TestFileState(p, IsFile),
                                            Rm(p),
                                            Skip)) // TODO(kgeffen) Links not yet covered!

      case Some("absent") => If(TestFileState(p, IsFile),
                                Rm(p),
                                Skip) // TODO(kgeffen) Links not yet covered

      /* missing: Create a file with content if content present
       * directory: if force is set then remove directory createFile
       *            and set content if present else ignore
       * file: if content set then set content else ignore
       * link: removelink, createfile and set content if present
       */
      case Some("file") if force => Block(If(TestFileState(p, IsDir),
                                             Rm(p),
                                             If(TestFileState(p, IsFile),
                                                Rm(p),
                                                Skip)),
                                          CreateFile(p, c)) // TODO(kgeffen) Links not yet covered

      case Some("file") => Block(If(TestFileState(p, IsFile),
                                    Rm(p),
                                    Skip),
                                 CreateFile(p, c)) // TODO(kgeffen) Links not yet covered

      /* Missing: Create new directory
       * Directory: Ignore
       * File: remove file and create directory
       * link: remove link and create directory
       */
      case Some("directory") => If(!TestFileState(p, DoesNotExist),
                                   Block(Rm(p), Mkdir(p)),
                                   Mkdir(p)) // TODO(kgeffen) Links not yet covered

      /*
       * Missing: create sym link with target
       * directory: if(force) removedir andThen createlink else ignore
       * file: delete file and create link
       * link: ignore
       */
      case Some("link") if force => Skip // TODO(kgeffen) Links not yet covered

        // Block(If(Exists(p),
        //                                        If(IsDir(p), RmDir(p),
        //                                           If(IsRegularFile(p), DeleteFile(p), Unlink(p))),
        //                                        Block()),
        //                                     Link(p, t))


      case Some("link") => Skip // TODO(kgeffen) Links not yet covered

        // Block(If(Exists(p),
        //                               If(IsRegularFile(p), DeleteFile(p),
        //                                  If(IsLink(p), Unlink(p), Block())),
        //                               Block()),
        //                            If(Not(Exists(p)), Link(p, t), Block()))


      case _ => throw new Exception(s"ensure attribute missing for file ${r.name}")
    }
  }


  def PuppetPackage(r: Resource): Expr = {

    val validEnsureVals = List("present", "installed", "absent", "purged", "held", "latest")

    val ensure = validVal(r, "ensure", validEnsureVals) getOrElse "installed"

    /* apt-file must be installed and should be updated */
    def packageFiles(): Set[Path] = {
      pkgcache.files(r.name) getOrElse
      (throw new Exception(s"Package not found: ${r.name}"))
    }

    ensure match {

      case "present" | "installed" | "latest" => {

        val files = pkgcache.files(r.name) getOrElse
          (throw new Exception(s"Package not found: ${r.name}"))

        val allpaths = paths.allpaths(files)

        val dirs = (allpaths -- files)
        /*
         * XXX(if sorting becomes a bottleneck): Bucket sort below but unreadable!
        val mkdirs = (dirs - paths.root).groupBy(_.getNameCount)
                                        .mapValues(_.toSeq)
                                        .toSeq
                                        .sortBy(_._1)
                                        .unzip._2
                                        .flatten
                                        .map(d => If(TestFileState(d, DoesNotExist), 
                                                     Mkdir(d), Skip)).toList
        */
        val mkdirs = (dirs - paths.root).toSeq.sortBy(_.getNameCount)
                                        .map(d => If(TestFileState(d, DoesNotExist), 
                                                     Mkdir(d), Skip)).toList

        val somecontent = Content("")
        val createfiles = files.map((f) => CreateFile(f, somecontent))

        val exprs = (mkdirs ++ createfiles)
        Block(exprs: _*)
      }

      case "absent" | "purged" => {

        val files = pkgcache.files(r.name) getOrElse
          (throw new Exception(s"Package not found: ${r.name}"))

        val exprs = files.map((f) => If(TestFileState(f, DoesNotExist), Skip, Rm(f))).toSeq
        Block(exprs: _*)
      }

      case "held"   => throw new Exception("NYI package held") // TODO
      case _ => throw new Exception(s"Invalid value for ensure: ${ensure}")
    }
  }

  def User(r: Resource): Expr = {

    val validEnsureVals = List("present", "absent", "role")

    import java.nio.file.{Files, LinkOption, Paths, Path}

    val ensure = validVal(r, "ensure", validEnsureVals) getOrElse "present"
    val gid = r.get[String]("gid")
    val groups = r.get[Array[Value]]("groups") getOrElse
                 { r.get[String]("groups").map((g) => Array((StringV(g): Value))) getOrElse
                 Array((UndefV: Value)) }

    val shell = r.get[String]("shell")
    val uid = r.get[String]("uid").map(_.toInt)
    // Directory must be created separately and is not checked for existence
    val home = r.get[String]("home")

    val comment = r.get[String]("comment")
    val expiry = r.get[String]("expiry")

    val allowdupe = validVal(r, "allowdupe", validBoolVals) getOrElse false
    val managehome = validVal(r, "managehome", validBoolVals) getOrElse false
    val system = validVal(r, "system", validBoolVals) getOrElse false

    def userExists(user: String): Boolean = {
      val (sts, _, _) = Cmd.exec(s"id -u $user")
      (sts == 0)
    }

    def gidExists(gid: String): Boolean = {
      val (sts, _, _) = Cmd.exec(s"getent group $gid")
      (sts == 0)
    }

    val u = Paths.get(s"/etc/users/${r.name}")
    val usettings = Paths.get(s"/etc/users/${r.name}/settings")
    val usettingscontent = Content("")
    val g = Paths.get(s"/etc/groups/${r.name}")
    val gsettings = Paths.get(s"/etc/groups/${r.name}/settings")
    val gsettingscontent = Content("")
    val h = Paths.get(home getOrElse s"/home/${r.name}")

    (ensure, managehome) match {

      case ("present", true) => If(TestFileState(u, DoesNotExist),
                                   Block(Mkdir(u),
                                         CreateFile(usettings, usettingscontent),
                                         If(TestFileState(g, DoesNotExist),
                                            Block(Mkdir(g), CreateFile(gsettings, gsettingscontent)),
                                            Skip),
                                         // TODO : Add to rest of groups
                                         If(TestFileState(h, DoesNotExist), Mkdir(h), Skip)),
                                   Skip)

      case ("present", false) => If(TestFileState(u, DoesNotExist),
                                    Block(Mkdir(u),
                                          CreateFile(usettings, usettingscontent),
                                          If(TestFileState(g, DoesNotExist),
                                             Block(Mkdir(g), CreateFile(gsettings, gsettingscontent)),
                                             Skip)
                                          // tODO: Add to rest of groups
                                          ),
                                    Skip)

      case ("absent", _) => If(!TestFileState(u, DoesNotExist),
                               Block(Rm(u),
                                     If(!TestFileState(g, DoesNotExist), Rm(g), Skip),
                                     If(!TestFileState(h, DoesNotExist), Rm(h), Skip)),
                               Skip)

      case (_, _) => throw new Exception(s"Unknown value present")
    }
  }


  def Group(r: Resource): Expr = {

    val validEnsureVals = List("present", "absent")

    val ensure = validVal(r, "ensure", validEnsureVals) getOrElse
      (throw new Exception(s"Group ${r.name} 'ensure' attribute missing"))

    /* Semantics of Group resource
     *
     * A group name is a directory by the name of the group located at location /etc/groups
     * Inside every directory there is a file called settings that contains configuration
     * data of every group
     *
     */
    val p = s"/etc/groups/${r.name}"
    val s = s"/etc/groups/${r.name}/settings"
    val c = Content("")

    ensure match {
      case "present" => If(TestFileState(p, DoesNotExist), 
                           Mkdir(p) >> CreateFile(s, c),
                           CreateFile(s, c))

      case "absent" => If(!TestFileState(p, DoesNotExist), Rm(p), Skip)

      case _ => throw new Exception(s"Invalid ensure value: $ensure")
    }
  }

  
  def Exec(r: Resource): Expr = {
     
    val command = r.get[String]("command") getOrElse r.name
    val creates = r.get[String]("creates")

    if(creates.isDefined) {
      val p = creates.get
      // If(!TestFileState(p, DoesNotExist), Skip, ShellExec(command))
      // TODO(kgeffen) Add ShellExec
      Skip
    }
    else { Skip /* ShellExec(command) */ } // TODO(kgeffen) Add ShellExec
  }

  def Service(r: Resource): Expr = {

    val validEnsureVals = List((StringV("stopped"): Value, "stopped"),
                               (BoolV(false): Value, "stopped"),
                               (StringV("running"): Value, "running"),
                               (BoolV(true): Value, "running"),
                               (UndefV: Value, "undef")).toMap
    val validBoolVal = List((StringV("true"): Value, true),
                            (StringV("false"): Value, false)).toMap
    val validEnableVals = validBoolVal
    val validHasRestartVals = validBoolVal
    val validHasStatusVals = validBoolVal

    val ensure = validVal(r, "ensure", validEnsureVals) getOrElse
      (throw new Exception(s"Service ${r.name} 'ensure' attribute missing"))
    val binary = r.get[String]("binary") getOrElse r.name
    val enable = validVal(r, "enable", validEnableVals) getOrElse false // Whether a service should be enabled at boot time.
    val flags  = r.get[String]("flags") getOrElse ""
    val hasrestart = validVal(r, "hasrestart", validHasRestartVals) getOrElse false
    // if a service's init script has a functional status command,
    val hasstatus = validVal(r, "hasstatus", validHasStatusVals) getOrElse true
    val path = r.get[String]("path") getOrElse "/etc/init.d/"
    /* pattern to search for in process table, used for stopping services that do not support init scripts
     * Also used for determining service status on those service whose init scripts do not include a status command
     */
    val pattern = r.get[String]("pattern") getOrElse binary
    val restart = r.get[String]("restart") // If not provided then service will be first stopped and then started
    val start = r.get[String]("start") getOrElse "start"
    val stop = r.get[String]("stop") getOrElse "stop"
    val status = r.get[String]("status")

    val mode = ensure match {
      case "stopped" => "stop"
      case "running" => "start"
      case "undef" => "start"
      case _ => throw new Exception(s"Invalid value $ensure for a service provider for ${r.name}")
    }

    val command = s"${path}/${binary} ${flags} ${mode}"
    // ShellExec(command)
    Skip // TODO: Add ShellExec
  }


  def Notify(r: Resource): Expr = { 

    val msg = r.get[String]("message") getOrElse r.name
    Skip
  }


  def apply(r: Resource): Expr = r.typ match {
    case "File" => File(r)
    case "Package" => PuppetPackage(r)
    case "User" => User(r)
    case "Notify" => Notify(r)
    case "Service" => Service(r)
    case "Group" => Group(r)
    case "Exec" => Exec(r)
    case _ => throw new Exception("Resource type \"%s\" not supported yet".format(r.typ))
  }
}
