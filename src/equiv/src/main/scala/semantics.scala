package equiv.semantics

import puppet.common.util._
import fsmodel.core._

import java.nio.file.{Paths, Path}

/*
 * Give filesystem semantics to resources
 *
 * Expresses resources in terms of file system changes
 */
object Provider {

  import puppet.common.resource._
  import puppet.common.resource.Extractor._
  import scala.collection.immutable.{Map, List}

  import java.nio.file.Path
  import scala.annotation.tailrec

  def ancestors(pathSet: Set[Path]): Set[Path] = {
    @tailrec
    def loop(p: Path, result: Set[Path]): Set[Path] = {
      // Check if we have already solved this problem
      if (!result(p)) {
        p.getParent match {
          case null => result
          case parent: Path => loop(parent, result + p.normalize)
        }
      }
      else {
        result
      }
    }

    pathSet.foldLeft(Set.empty[Path]) { (pathSet, path) => loop(path, pathSet) }
  }

  def apply(r: Resource): Provider = r.typ match {
    case "File" => File(r)
    case "Package" => PuppetPackage(r)
    case "User" => User(r)
    // case "Notify" => Notify(r)
    case "Service" => Service(r)
    case "Group" => Group(r)
    case "Exec" => Exec(r)
    case _ => throw new Exception("Resource type \"%s\" not supported yet".format(r.typ))
  }

  sealed abstract class Provider (val r: Resource) {
    val name = r.name

    protected val validBoolVals = List ((BoolV(true): Value, true),
                                        (BoolV(false): Value, false),
                                        (StringV("yes"): Value, true),
                                        (StringV("no"): Value, false)).toMap

    def toFSOps(): Expr

    protected def validVal[T](property: String, options: Map[Value, T]): Option[T] = {
      r.getRawVal(property).map(options.get(_)).flatten
    }

    protected def validVal(property: String, options: List[String]): Option[String] = {
      val m = options.map((o) => (StringV(o): Value, o)).toMap
      validVal(property, m)
    }
  }

  case class File(res: Resource) extends Provider(res) {
    private val validEnsureVals = List("present", "absent", "file", "directory", "link")

    val path = r.get[String]("path") getOrElse name
    val source = r.get[String]("source")
    val ensure = validVal("ensure", validEnsureVals)
    val force = validVal("force", validBoolVals) getOrElse false
    val purge = validVal("purge", validBoolVals) getOrElse false
    val target = r.get[String]("target")
    val content = r.get[String]("content")

    // TODO: Ignoring ownership and permissions for now
    // TODO : Ignoring source attribute
    def toFSOps: Expr = {

       val p = Paths.get(path)
       val c = Content(content getOrElse "")
       val t = Paths.get(target getOrElse "/tmp/")

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

        /*
        """
        if(exists(p)) {
          if(isregularfile(p)) {
            delete(p)
            create(p, c)
          }
        }
        else {
          create(p, c)
        }
        """
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
         /*
         """
         if(exists(p)) {
           if(isdir(p)) rmdir(p) // force param has to be set in resource
           else if(islink(p)) unlink(p)
           else delete(p)
         }
         """
         */

        case Some("absent") if force => If(TestFileState(p, IsDir),
                                           Rm(p),
                                           If(TestFileState(p, IsFile),
                                              Rm(p),
                                              Skip)) // TODO(kgeffen) Links not yet covered!

         /*
         """
         if(exists(p)) {
           if(islink(p)) unlink(p)
           else if(regularfile(p)) delete(p)
           // Ignore directory even if its exists when force is not set
         }
         """
         */
        case Some("absent") => If(TestFileState(p, IsFile),
                                  Rm(p),
                                  Skip) // TODO(kgeffen) Links not yet covered

        /* missing: Create a file with content if content present
         * directory: if force is set then remove directory createFile and set content if present else ignore
         * file: if content set then set content else ignore
         * link: removelink, createfile and set content if present
         */
         /*
        """
        if (exists(p)) {
          if (isdir(p)) rmdir(p)
          else if (islink(p)) unlink(p)
          else delete(p)
        }
        create(p, c)
        """
        */
        case Some("file") if force => Block(If(TestFileState(p, IsDir),
                                               Rm(p),
                                               If(TestFileState(p, IsFile),
                                                  Rm(p),
                                                  Skip)),
                                            CreateFile(p, c)) // TODO(kgeffen) Links not yet covered

       
       /*
       """
       if(exists(p)) {
         if(isregularfile(p)) delete(p)
         else if(islink(p)) unlink(p)
       }

       if(!exists(p)) create(p, c)
       """ 
       */
       case Some("file") => Block(If(TestFileState(p, IsFile),
                                     Rm(p),
                                     Skip),
                                  CreateFile(p, c)) // TODO(kgeffen) Links not yet covered

        /* Missing: Create new directory
         * Directory: Ignore
         * File: remove file and create directory
         * link: remove link and create directory
         */

        /*
        """
        if(exists(p)) {
          if(isregularfile(p)) delete(p)
          else if(islink(p)) unlink(p)
        }
        if(!exists(p)) mkdir(p)
        """
        */
        case Some("directory") => If(!TestFileState(p, DoesNotExist),
                                     Block(Rm(p), Mkdir(p)),
                                     MkDir(p)) // TODO(kgeffen) Links not yet covered

        /*
         * Missing: create sym link with target
         * directory: if(force) removedir andThen createlink else ignore
         * file: delete file and create link
         * link: ignore
         */
         /*
         """
         if (exist(p)) {
           if (isdir(p)) rmdir(p)
           else if (isregularfile(p)) delete(p)
           else unlink(p)
         }
         link(p, t)
         """
         */
        case Some("link") if force => Skip // TODO(kgeffen) Links not yet covered

        // Block(If(Exists(p),
        //                                        If(IsDir(p), RmDir(p),
        //                                           If(IsRegularFile(p), DeleteFile(p), Unlink(p))),
        //                                        Block()),
        //                                     Link(p, t))
                                            

        /*
        """
        if(exists(p)) {
          if(isregularfile(p)) delete(p),
          else if(islink(p)) unlink(p)
        }
        if(!exists(p)) link(p, t)
        */
        case Some("link") => Skip // TODO(kgeffen) Links not yet covered

        // Block(If(Exists(p),
        //                               If(IsRegularFile(p), DeleteFile(p),
        //                                  If(IsLink(p), Unlink(p), Block())),
        //                               Block()),
        //                            If(Not(Exists(p)), Link(p, t), Block()))


        case _ => println(name); println(ensure); throw new Exception("One or more required attribute missing")
      }
    }
  }

  case class PuppetPackage(res: Resource) extends Provider(res) {

    private val validEnsureVals = List("present", "installed", "absent", "purged", "held", "latest")

    val ensure = validVal("ensure", validEnsureVals)
    
    /*
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
    */

    /* apt-file must be installed and should be updated */
    private def files: Set[Path] = {

      val cmd = s"apt-file -F list $name"
      val (sts, out, err) = Cmd.exec(cmd)
      if (0 == sts) {
        out.lines.toList.map((l) => Paths.get(l.split(" ")(1)).normalize).toSet
      }
      else {
        throw new Exception(s"$cmd failed: $err")
      }
    }

    def toFSOps: Expr = {

      import scala.collection.SortedSet

      // Arrange dirs by closest first
      val orderby = Ordering.by[Path, Int](_.getNameCount)

      val root = Paths.get("/")
      val allpaths = SortedSet[Path]()(orderby) ++ equiv.ancestors(files)
      val dirs = (allpaths -- files)

      ensure match {
        case Some("present") | Some("installed") | Some("latest") => {

          val somecontent = Content("")
          val mkdirs = (dirs - root).map(d => If(TestFileState(d, DoesNotExist), MkDir(d), Skip)).toList
          val createfiles = files.map((f) => CreateFile(f, somecontent))
          val exprs = (mkdirs ++ createfiles)
          Block(exprs: _*)
        }

        case Some("absent") | Some("purged") => {
          val exprs = files.map(Rm(_)).toSeq
          Block(exprs: _*)
        }

        case Some("held")   => throw new Exception("NYI package held") // TODO
        case _ => throw new Exception("One or more required attribute is missing")
      }
    }
  }

  case class User(res: Resource) extends Provider(res) {

    private val validEnsureVals = List("present", "absent", "role")

    import java.nio.file.{Files, LinkOption, Paths, Path}

    val ensure = validVal("ensure", validEnsureVals) getOrElse "present"
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

    def toFSOps (): Expr = {

      val u = Paths.get(s"/etc/users/$name")
      val usettings = Paths.get(s"/etc/users/$name/settings")
      val usettingscontent = Content("")
      val g = Paths.get(s"/etc/groups/$name")
      val gsettings = Paths.get(s"/etc/groups/$name/settings")
      val gsettingscontent = Content("")
      val h = Paths.get(home getOrElse s"/home/$name")

      (ensure, managehome) match {

        /*
        """
        u = /etc/users/name
        g = /etc/groups/name
        if (!exists(u) {
          mkdir(u)
          create(u/shadow, c)
          create(u/passwd, c')

          // Create a group by the name of user if it already does not exists
          if(!exists(g)) {
            mkdir(g)
            createFile(g/settings, c'')
          }

          // Add user to every group specified


          // create home directory if it not already exists
          if (!exists(h)) {
            mkdir(h)
            // Assume a blank home directory
          }
        }
        """
        */

        case ("present", true) => If(TestFileState(u, DoesNotExist),
                                     Block(MkDir(u),
                                           CreateFile(usettings, usettingscontent),
                                           If(TestFileState(g, DoesNotExist),
                                              Block(MkDir(g), CreateFile(gsettings, gsettingscontent)),
                                              Skip),
                                           // TODO : Add to rest of groups
                                           If(TestFileState(h, DoesNotExist), MkDir(h), Skip)),
                                     Skip)

        case ("present", false) => If(TestFileState(u, DoesNotExist),
                                      Block(MkDir(u),
                                            CreateFile(usettings, usettingscontent),
                                            If(TestFileState(g, DoesNotExist),
                                               Block(MkDir(g), CreateFile(gsettings, gsettingscontent)),
                                               Skip)
                                            // tODO: Add to rest of groups
                                            ),
                                      Skip)

        /*
        """
        if(exists(u)) {
          rmdir(u)
          if(exists(g)) {
            rmdir(g)
          }
          if(exists(h)) {
            rmdir(h)
          }
        }
        """
        */

        case ("absent", _) => If(!TestFileState(u, DoesNotExist),
                                 Block(Rm(u),
                                       If(!TestFileState(g, DoesNotExist), Rm(g), Skip),
                                       If(!TestFileState(h, DoesNotExist), Rm(h), Skip)),
                                 Skip)

        case (_, _) => throw new Exception(s"Unknown value present")
      }
    }
  }

  /*
  case class Notify(res: Resource) extends Provider(res) {

    private val msg = r.get[String]("message") getOrElse name

    def realize() { println(msg) }
  }
  */

  case class Service(res: Resource) extends Provider(res) {
    private val validEnsureVals = List((StringV("stopped"): Value, "stopped"),
                                       (BoolV(false): Value, "stopped"),
                                       (StringV("running"): Value, "running"),
                                       (BoolV(true): Value, "running"),
                                       (UndefV: Value, "undef")).toMap
    private val validBoolVal = List((StringV("true"): Value, true),
                                    (StringV("false"): Value, false)).toMap
    private val validEnableVals = validBoolVal
    private val validHasRestartVals = validBoolVal
    private val validHasStatusVals = validBoolVal
     
    val ensure = validVal("ensure", validEnsureVals) getOrElse (throw new Exception(s"Service $name 'ensure' attribute missing"))
    val binary = r.get[String]("binary") getOrElse name
    val enable = validVal("enable", validEnableVals) getOrElse false // Whether a service should be enabled at boot time.
    val flags  = r.get[String]("flags") getOrElse ""
    val hasrestart = validVal("hasrestart", validHasRestartVals) getOrElse false
    // if a service's init script has a functional status command,
    val hasstatus = validVal("hasstatus", validHasStatusVals) getOrElse true
    val path = r.get[String]("path") getOrElse "/etc/init.d/"
    /* pattern to search for in process table, used for stopping services that do not support init scripts
     * Also used for determining service status on those service whose init scripts do not include a status command
     */
    val pattern = r.get[String]("pattern") getOrElse binary
    val restart = r.get[String]("restart") // If not provided then service will be first stopped and then started
    val start = r.get[String]("start") getOrElse "start"
    val stop = r.get[String]("stop") getOrElse "stop"
    val status = r.get[String]("status")

    def toFSOps(): Expr = {

      val mode = ensure match {
        case "stopped" => "stop"
        case "running" => "start"
        case "undef" => "start"
        case _ => throw new Exception(s"Invalid value $ensure for a service provider for $name")
      }

      val command = s"${path}/${binary} ${flags} ${mode}"
      ShellExec(command)
    }
  }

  case class Group(res: Resource) extends Provider(res) {
    private val validEnsureVals = List("present", "absent")

    val ensure = validVal("ensure", validEnsureVals) getOrElse (throw new Exception(s"Group $name 'ensure' attribute missing"))

    /* Semantics of Group resource
     *
     * A group name is a directory by the name of the group located at location /etc/groups
     * Inside every directory there is a file called settings that contains configuration 
     * data of every group
     *
     */
    def toFSOps (): Expr = {

      val p = Paths.get(s"/etc/groups/$name")
      val s = Paths.get(s"/etc/groups/$name/settings")
      val c = Content("")

      ensure match {
        /*
        """
        if(!exists(p)) {
          mkdir(p)
          create(p/settings, c)
        }
        """
        */
        case "present" => If(TestFileState(p, DoesNotExist), Block(MkDir(p), CreateFile(s, c)), Skip)

        /*
        """
        if(exists(p)) rmdir(p)
        """
        */
        case "absent" => If(!TestFileState(p, DoesNotExist), Rm(p), Skip)

        case _ => throw new Exception(s"Invalid ensure value: $ensure")
      }
    }
  }

  case class Exec(res: Resource) extends Provider(res) {

    val command = r.get[String]("command") getOrElse name
    val creates = r.get[String]("creates")

    def toFSOps (): Expr = {

      if(creates.isDefined) {
        val p = Paths.get(creates.get)
        // If(!TestFileState(p, DoesNotExist), Skip, ShellExec(command))
        // TODO(kgeffen) Add ShellExec
        Skip
      }
      else { Skip /* ShellExec(command) */ } // TODO(kgeffen) Add ShellExec
    }
  }
}
