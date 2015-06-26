package rehearsal.ppmodel

private[ppmodel] object PostCondition {


  import rehearsal._
  import puppet.graph._
  import rehearsal.fsmodel._
  import FSSyntax._
  import puppet.graph.Implicits._
  import rehearsal.fsmodel.Implicits._
  import java.nio.file.Paths

  val pkgcache = PackageCache()

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

  def File(r: Resource): Pred = {
    val validEnsureVals = List("present", "absent", "file", "directory", "link")

    val path = r.get[String]("path") getOrElse r.name
    val ensure = validVal(r, "ensure", validEnsureVals) orElse {
      if (r.get[String]("content").isDefined) Some("present") else None
    }
    val force = validVal(r, "force", validBoolVals) getOrElse false

    val _ensure = if (ensure.isDefined) ensure
                  else if (r.get[String]("source").isDefined) Some("file")
                  else None

    _ensure match {
      case Some("present") => TestFileState(path, IsFile)
      case Some("absent") if force => TestFileState(path, DoesNotExist)
      case Some("absent") => !TestFileState(path, IsFile)
      case Some("file") if force => TestFileState(path, IsFile)
      case Some("file") => !TestFileState(path, DoesNotExist)
      case Some("directory") => TestFileState(path, IsDir)
      case _ => throw Unexpected(s"ensure attribute missing for file ${r.name}")
    }
  }

  def PuppetPackage(r: Resource): Pred = {
    val validEnsureVals = List("present", "installed", "absent", "purged", "held", "latest")

    val ensure = validVal(r, "ensure", validEnsureVals) getOrElse "installed"
    val provider = r.get[String]("provider")

    if (provider.isDefined && provider.get != "apt") {
      throw NotImplemented(s"""package(${r.name}): "${provider.get}" provider not supported""")
    }

    ensure match {
      case "present" | "installed" | "latest" => {
        val files = pkgcache.files(r.name) getOrElse
          (throw Unexpected(s"Package not found: ${r.name}"))

        val dirs = (allpaths(files) -- files)

        val dirPreds = dirs.toSeq.map(TestFileState(_, IsDir))
        val filePreds = files.toSeq.map(TestFileState(_, IsFile))
        val preds = dirPreds ++ filePreds

        And(preds: _*)
      }
      case "absent" | "purged" => {
        val files = pkgcache.files(r.name) getOrElse
          (throw Unexpected(s"Package not found: ${r.name}"))

        And(files.toSeq.map(TestFileState(_, DoesNotExist)): _*)
      }
      case _ => throw Unexpected(s"Invalid value for ensure: ${ensure}")
    }
  }

  def User(r: Resource): Pred = {
    val validEnsureVals = List("present", "absent", "role")

    val ensure = validVal(r, "ensure", validEnsureVals) getOrElse "present"
    val home = r.get[String]("home")
    val managehome = validVal(r, "managehome", validBoolVals) getOrElse false

    val u = Paths.get(s"/etc/users/${r.name}")
    val usets = Paths.get(s"/etc/users/${r.name}/settings")
    val g = Paths.get(s"/etc/groups/${r.name}")
    val gsets = Paths.get(s"/etc/groups/${r.name}/settings")
    val h = Paths.get(home getOrElse s"/home/${r.name}")

    (ensure, managehome) match {
      case ("present", true) => TestFileState(u, IsDir) && TestFileState(g, IsDir) &&
                                TestFileState(h, IsDir) && TestFileState(usets, IsFile) &&
                                TestFileState(gsets, IsFile)
      case ("present", false) => TestFileState(u, IsDir) && TestFileState(g, IsDir) &&
                                 TestFileState(usets, IsFile) && TestFileState(gsets, IsFile)
      case ("absent", _) => TestFileState(u, DoesNotExist) && TestFileState(usets, DoesNotExist) &&
                            TestFileState(g, DoesNotExist) && TestFileState(gsets, DoesNotExist) &&
                            TestFileState(h, DoesNotExist)
      case (_, _) => throw Unexpected(s"Unknown value for ensure: ${ensure}")
    }
  }

  def Group(r: Resource): Pred = {
    val validEnsureVals = List("present", "absent")

    val ensure = validVal(r, "ensure", validEnsureVals) getOrElse
      (throw Unexpected(s"Group ${r.name} 'ensure' attribute missing"))

    /* Semantics of Group resource
     *
     * A group name is a directory by the name of the group located at
     * location /etc/groups. Inside every directory there is a file called
     * settings that contains configuration data of every group
     *
     */
    val p = s"/etc/groups/${r.name}"
    val s = s"/etc/groups/${r.name}/settings"

    ensure match {
      case "present" => TestFileState(p, IsDir) && TestFileState(s, IsFile)
      case "absent" => TestFileState(p, DoesNotExist) && TestFileState(s, DoesNotExist)
      case _ => throw Unexpected(s"Invalid ensure value: $ensure")
    }
  }

  def apply(r: Resource): Pred = r.typ match {
    case "File" => File(r)
    case "Package" => PuppetPackage(r)
    case "User" => User(r)
    case "Group" => Group(r)
    case _ => throw NotImplemented("Resource type \"%s\" not supported yet".format(r.typ))
  }
}
