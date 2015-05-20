package rehearsal.ppmodel

import puppet.common.util._
import rehearsal.fsmodel._
import rehearsal.fsmodel.Implicits._

/*
 * Give filesystem semantics to resources
 *
 * Expresses resources in terms of file system changes
 */
private[ppmodel] object ResourceToExpr {

  import java.nio.file.{Path, Files, Paths}

  import puppet.common.resource._
  import puppet.common.resource.Extractor._

  val pkgcache = {
    val benchmarksDir = Paths.get("benchmarks")
    if (!Files.isDirectory(benchmarksDir)) {
      Files.createDirectory(benchmarksDir)
    }
    val pkgcacheDir = benchmarksDir.resolve("pkgcache")
    if (!Files.isDirectory(pkgcacheDir)) {
      Files.createDirectory(pkgcacheDir)
    }
    new PackageCache(pkgcacheDir.toString)
  }

  def PackageDependencies(pkg: String): List[String] = {
    val cmd = s"""apt-rdepends --show=depends $pkg | grep -v '^ ' | grep -v $pkg"""
    val (sts, out, err) = Cmd.exec(cmd)
    /*  Toposort
     *  Among dependent packages of this package, apt-get will install the
     *  package with all its dependencies present first(in a reverse
     *  topological sort order)
     */
     out.lines.toList
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
    } orElse {
      if(source.isDefined) Some("file") else None
    }
    val force = validVal(r, "force", validBoolVals) getOrElse false
    val purge = validVal(r, "purge", validBoolVals) getOrElse false
    val target = r.get[String]("target")
    val owner = r.get[String]("owner")
    val provider = r.get[String]("provider")
    val mode = r.get[String]("mode")

    val props: Map[String, Option[String]] = Map(
      "path" -> Some(path),
      "content" -> content,
      "source" -> source,
      "ensure" -> ensure,
      "force" -> Some(force.toString),
      "purge" -> Some(purge.toString)
    )

    (props("ensure"),
     props("path"),
     props("content"),
     props("source"),
     props("force")) match {
       case (Some("present"), Some(p), Some(c), None, _) =>  If(TestFileState(p, IsFile),
                                                                Block(Rm(p), CreateFile(p, c)),
                                                                If(TestFileState(p, DoesNotExist),
                                                                   CreateFile(p, c),
                                                                   Skip))

      case (Some("present"), Some(p), None, Some(c), _) => If(TestFileState(p, IsFile),
                                                              Block(Rm(p), CreateFile(p, c)),
                                                              If(TestFileState(p, DoesNotExist),
                                                                 CreateFile(p, c),
                                                                 Skip))

       case (Some("present"), Some(p), None, None, _) =>  If(TestFileState(p, IsFile),
                                                             Block(Rm(p), CreateFile(p, "")),
                                                             If(TestFileState(p, DoesNotExist),
                                                                CreateFile(p, ""),
                                                                Skip))


       case (Some("absent"), Some(p), _, _, Some("true")) => If(TestFileState(p, IsDir),
                                                                Rm(p),
                                                                If(TestFileState(p, IsFile), Rm(p), Skip))

       case (Some("absent"), Some(p), _, _, Some("false")) => If(TestFileState(p, IsFile), Rm(p), Skip)

       case (Some("file"), Some(p), Some(c), None, Some("true")) => Block(If(TestFileState(p, IsDir),
                                                                             Rm(p),
                                                                             If(TestFileState(p, IsFile), Rm(p), Skip)),
                                                                          CreateFile(p, c))

       case (Some("file"), Some(p), None, Some(c), Some("true")) => Block(If(TestFileState(p, IsDir),
                                                                             Rm(p),
                                                                             If(TestFileState(p, IsFile), Rm(p), Skip)),
                                                                          CreateFile(p, c))

       case (Some("file"), Some(p), None, None, Some("true")) => Block(If(TestFileState(p, IsDir),
                                                                          Rm(p),
                                                                          If(TestFileState(p, IsFile), Rm(p), Skip)),
                                                                       CreateFile(p, ""))

       case (Some("file"), Some(p), Some(c), None, Some("false")) => Block(If(TestFileState(p, IsFile), Rm(p), Skip),
                                                                           CreateFile(p, c))

       case (Some("file"), Some(p), None, Some(c), Some("false")) => Block(If(TestFileState(p, IsFile), Rm(p), Skip),
                                                                           CreateFile(p, c))

       case (Some("file"), Some(p), None, None, Some("false")) => Block(If(TestFileState(p, IsFile), Rm(p), Skip),
                                                                           CreateFile(p, ""))

       case (Some("directory"), Some(p), _, _, _) => If(TestFileState(p, IsDir),
                                                        Skip,
                                                        If(TestFileState(p, IsFile),
                                                            Rm(p) >> Mkdir(p),
                                                            Mkdir(p)))


       case _ => throw new Exception(s"ensure attribute missing for file ${r.name}")
     }

    // if(_ensure.isDefined && _ensure.get == "link") {
    //   throw new Exception(s"""file(${r.name}): "${_ensure.get}" ensure not supported""")
    // }

    // if(source.isDefined) {
    //   throw new Exception(s"""file(${r.name}): source attribute not supported""")
    // }
    // if(provider.isDefined && provider.get != "posix") {
    //   throw new Exception(s"""file(${r.name}): "${provider.get}" provider not supported""")
    // }
    // if(mode.isDefined) {
    //   throw new Exception(s"""file(${r.name}): "mode" attribute not supported""")
    // }
    // if(owner.isDefined) {
    //   throw new Exception(s"""file(${r.name}): "owner" attribute not supported""")
    // }
  }


  def installToFSExpr(name: String): Option[Expr] = {
    val files = pkgcache.files(name) getOrElse {
      // Maybe a virtual package
      return None
    }

    val all_paths = allpaths(files)
    val dirs = (all_paths -- files)

    val mkdirs = (dirs - root).toSeq.sortBy(_.getNameCount)
                              .map(d => If(TestFileState(d, DoesNotExist),
                                           Mkdir(d), Skip)).toList
    val somecontent = ""
    val createfiles = files.map((f) => CreateFile(f, somecontent))

    val exprs = (mkdirs ++ createfiles)
    val block = Block(exprs: _*)

    // check if package is already installed
    Some(If(TestFileState(s"/packages/${name}", DoesNotExist), Skip, block))
  }


  def PuppetPackage(r: Resource): Expr = {

    val validEnsureVals = List("present", "installed", "absent", "purged", "held", "latest")

    val ensure = validVal(r, "ensure", validEnsureVals) getOrElse "installed"
    val provider = r.get[String]("provider")

    if(provider.isDefined && provider.get != "apt") {
      throw new Exception(s"""package(${r.name}): "${provider.get}" provider not supported""")
    }

    ensure match {

      case "present" | "installed" | "latest" => {

        val deps = PackageDependencies(r.name)
        val depExprs = deps.map(d => installToFSExpr(d)).flatten

        val exprs = installToFSExpr(r.name) getOrElse
          (throw new Exception(s"Package not found: ${r.name}"))
        // Append at end
        val block = depExprs :+ exprs
        Block(block: _*)
      }

      case "absent" | "purged" => {

        val files = pkgcache.files(r.name) getOrElse
          (throw new Exception(s"Package not found: ${r.name}"))

        val exprs = files.map((f) => If(TestFileState(f, DoesNotExist),
                                        Skip, Rm(f))).toSeq

        val pkgInstallInfoPath = s"/packages/${r.name}"
        // Append at end
        exprs :+ If(TestFileState(pkgInstallInfoPath, DoesNotExist),
                    Skip, Rm(pkgInstallInfoPath))
        Block(exprs: _*)
      }

      case "held" => throw new Exception("NYI package held") // TODO
      case _ => throw new Exception(s"Invalid value for ensure: ${ensure}")
    }
  }

  def User(r: Resource): Expr = {

    val validEnsureVals = List("present", "absent", "role")

    import java.nio.file.{Files, LinkOption, Paths, Path}

    val ensure = validVal(r, "ensure", validEnsureVals) getOrElse "present"
    val gid = r.get[String]("gid")
    val groups = r.get[Array[Value]]("groups") getOrElse {
      r.get[String]("groups").map((g) => Array((StringV(g): Value))) getOrElse {
        Array((UndefV: Value))
      }
    }

    val shell = r.get[String]("shell")
    val uid = r.get[String]("uid").map(_.toInt)
    // Directory must be created separately and is not checked for existence
    val home = r.get[String]("home")

    val comment = r.get[String]("comment")
    val expiry = r.get[String]("expiry")

    val allowdupe = validVal(r, "allowdupe", validBoolVals) getOrElse false
    val managehome = validVal(r, "managehome", validBoolVals) getOrElse false
    val system = validVal(r, "system", validBoolVals) getOrElse false
    val provider = r.get[String]("provider")

    def userExists(user: String): Boolean = {
      val (sts, _, _) = Cmd.exec(s"id -u $user")
      (sts == 0)
    }

    def gidExists(gid: String): Boolean = {
      val (sts, _, _) = Cmd.exec(s"getent group $gid")
      (sts == 0)
    }

    if(provider.isDefined && provider.get != "useradd") {
      throw new Exception(s"""user(${r.name}): "${provider.get}" provider not supported""")
    }

    val u = Paths.get(s"/etc/users/${r.name}")
    val usettings = Paths.get(s"/etc/users/${r.name}/settings")
    val usettingscontent = ""
    val g = Paths.get(s"/etc/groups/${r.name}")
    val gsettings = Paths.get(s"/etc/groups/${r.name}/settings")
    val gsettingscontent = ""
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

    val provider = r.get[String]("provider")

    if(provider.isDefined && provider.get != "groupadd") {
      throw new Exception(s"""group(${r.name}): "${provider.get}" provider not supported""")
    }

    /* Semantics of Group resource
     *
     * A group name is a directory by the name of the group located at
     * location /etc/groups. Inside every directory there is a file called
     * settings that contains configuration data of every group
     *
     */
    val p = s"/etc/groups/${r.name}"
    val s = s"/etc/groups/${r.name}/settings"
//    val c = Content("")
    val c = ""

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
    val provider = r.get[String]("provider")

    if(provider.isDefined && provider.get == "windows") {
      throw new Exception(s"exec(${r.name}): windows command execution not supported")
    }

    if(creates.isDefined) {
      val p = creates.get
      /* TODO(nimish): Semantics of shell*/
      If(!TestFileState(p, DoesNotExist), Skip, Skip)
    }
    else { Skip /* TODO(nimish): Semantics of shell */ }
  }

  def Service(r: Resource): Expr = {

    val validEnsureVals: Map[Value, String] = Map(
      StringV("stopped") -> "stopped",
      BoolV(false) -> "stopped",
      StringV("running") -> "running",
      BoolV(true) -> "running",
      UndefV -> "undef"
    )
    val validBoolVal: Map[Value, Boolean] = Map(
      StringV("true") -> true,
      StringV("false") -> false
    )
    val validEnableVals = List("true", "false", "manual")
    val validHasRestartVals = validBoolVal
    val validHasStatusVals = validBoolVal

    val ensure = validVal(r, "ensure", validEnsureVals) getOrElse
      (throw new Exception(s"Service ${r.name} 'ensure' attribute missing"))
    val binary = r.get[String]("binary") getOrElse r.name
    // Decides whether a service should be enabled at boot time
    val enable = validVal(r, "enable", validEnableVals)
    val flags  = r.get[String]("flags") getOrElse ""
    val hasrestart = validVal(r, "hasrestart", validHasRestartVals) getOrElse false
    // if a service's init script has a functional status command,
    val hasstatus = validVal(r, "hasstatus", validHasStatusVals) getOrElse true
    val path = r.get[String]("path") getOrElse "/etc/init.d/"
    /* pattern to search for in process table, used for stopping services
     * that do not support init scripts
     *
     * Also used for determining service status on those service whose init
     * scripts do not include a status command
     */
    val pattern = r.get[String]("pattern") getOrElse binary
    // If not provided then service will be first stopped and then started
    val restart = r.get[String]("restart")
    val start = r.get[String]("start") getOrElse "start"
    val stop = r.get[String]("stop") getOrElse "stop"
    val status = r.get[String]("status")
    val provider = r.get[String]("provider")

    if (enable.isDefined && enable.get == "manual") {
      throw new Exception(s"""service(${r.name}): "manual" enable defined only for windows based system""")
    }

    if(provider.isDefined && provider.get != "upstart") {
      throw new Exception(s"""service(${r.name}: ${provider.get} unsupported on Ubuntu""")
    }

    val mode = ensure match {
      case "stopped" => "stop"
      case "running" => "start"
      case "undef" => "start"
      case _ => throw new Exception(s"service(${r.name}): Invalid value $ensure")
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
