package rehearsal.ppmodel

import puppet.common.util._
import rehearsal._
import rehearsal.fsmodel.{Expr, Skip}
import rehearsal.fsmodel.Implicits._
import ppmodel.{ResourceModel => R}
/*
 * Give filesystem semantics to resources
 *
 * Expresses resources in terms of file system changes
 */
private[ppmodel] object ResourceToExpr {

  import java.nio.file.{Path, Files, Paths}

  import puppet.graph._
  import puppet.graph.Implicits._

  val pkgcache = PackageCache()

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

    (props("ensure"), props("path"), props("content"), props("source"),
     props("force")) match {
       case (Some("present"), Some(p), Some(c), None, _) =>  R.File(p, c, false).compile
        case (Some("present"), Some(p), None, Some(c), _) => R.File(p, c, false).compile
        case (Some("present"), Some(p), None, None, _) => R.File(p, "", false).compile
        case (Some("absent"), Some(p), _, _, Some("true")) => R.AbsentPath(p, true).compile
        case (Some("absent"), Some(p), _, _, Some("false")) => R.AbsentPath(p, false).compile
        case (Some("file"), Some(p), Some(c), None, Some("true")) => R.File(p, c, true).compile
        case (Some("file"), Some(p), None, Some(c), Some("true")) => R.File(p, c, true).compile
        case (Some("file"), Some(p), None, None, Some("true")) => R.File(p, "", true).compile
        case (Some("file"), Some(p), Some(c), None, Some("false")) =>  R.EnsureFile(p, c).compile
        case (Some("file"), Some(p), None, Some(c), Some("false")) => R.EnsureFile(p, c).compile
        case (Some("file"), Some(p), None, None, Some("false")) => R.EnsureFile(p, "").compile
        case (Some("directory"), Some(p), _, _, _) => R.Directory(p).compile
       case _ => throw new Exception(s"ensure attribute missing for file ${r.name}")
     }
  }

  def PuppetPackage(r: Resource): Expr = {

    val validEnsureVals = List("present", "installed", "absent", "purged", "held", "latest")

    val ensure = validVal(r, "ensure", validEnsureVals) getOrElse "installed"
    val provider = r.get[String]("provider")

    if(provider.isDefined && provider.get != "apt") {
      throw new Exception(s"""package(${r.name}): "${provider.get}" provider not supported""")
    }

    ensure match {
      case "present" | "installed" | "latest" => R.Package(r.name, true).compile
      case "absent" | "purged" => R.Package(r.name, false).compile
      case "held" => throw new Exception("NYI package held") // TODO
      case _ => throw new Exception(s"Invalid value for ensure: ${ensure}")
    }
  }

  def User(r: Resource): Expr = {
    val validEnsureVals = List("present", "absent", "role")
    val ensure = validVal(r, "ensure", validEnsureVals) getOrElse "present"
    val managehome = validVal(r, "managehome", validBoolVals) getOrElse false
    if (r.get[String]("provider").getOrElse("useradd") != "useradd") {
      throw Unsupported(s"user(${r.name}): provider not supported")
    }
    (ensure, managehome) match {
      case ("present", true) => R.User(r.name, true, true).compile
      case ("present", false) => R.User(r.name, true, false).compile
      case ("absent", _) => R.User(r.name, false, managehome).compile
      case (_, _) => throw Unexpected(s"value for ensure: $ensure")
    }
  }

  def Group(r: Resource): Expr = {
    val validEnsureVals = List("present", "absent")
    val ensure = validVal(r, "ensure", validEnsureVals) getOrElse {
      throw Unexpected(s"group ${r.name} 'ensure' attribute missing")
    }
    val provider = r.get[String]("provider")
    if (provider.getOrElse("groupadd") != "groupadd") {
      throw Unsupported(s"""group(${r.name}): "${provider.get}" provider not supported""")
    }
    ensure match {
      case "present" => R.Group(r.name, true).compile
      case "absent" => R.Group(r.name, false).compile
      case _ => throw Unexpected(s"ensure value is $ensure")
    }
  }

  def apply(r: Resource): Expr = r.typ match {
    case "File" => File(r)
    case "Package" => PuppetPackage(r)
    case "User" => User(r)
    case "Notify" => Skip
    case "Service" => {
      println("Warning: found a service resource, but treating as Skip")
      Skip
    }
    case "Group" => Group(r)
    case "Exec" => {
      println("WARNING: found an exec resource, but treating as Skip")
      Skip
    }
    case _ => throw Unsupported("Resource type \"%s\" not supported yet".format(r.typ))
  }
}
