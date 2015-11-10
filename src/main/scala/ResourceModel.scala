package rehearsal

object ResourceModel {

  import java.nio.file.{Path, Paths}
  import scala.collection.immutable.Set
  import FSSyntax._
  import rehearsal.Implicits._
  import scalaj.http.Http

  sealed trait Content
  case class CInline(src: String) extends Content
  case class CFile(src: String) extends Content

  sealed trait Res {
    def compile(distro: String): Expr = ResourceModel.compile(this, distro)
  }

  case class File(path: Path, content: Content, force: Boolean) extends Res
  case class EnsureFile(path: Path, content: Content) extends Res
  case class AbsentPath(path: Path, force: Boolean) extends Res
  case class Directory(path: Path) extends Res
  case class Package(name: String, present: Boolean) extends Res
  case class Group(name: String, present: Boolean) extends Res
  case class User(name: String, present: Boolean, manageHome: Boolean) extends Res
  case class Service(name: String) extends Res {
    val path = s"/etc/init.d/$name"
  }

  case class SshAuthorizedKey(user: String, present: Boolean, name: String, key: String) extends Res {
    val keyPath = s"/home/$user/.ssh/$name"
  }

  case object Notify extends Res

  def queryPackage(distro: String, pkg: String): Option[Set[Path]] = {
    val resp = Http(s"http://104.197.140.244:8080/query/$distro/$pkg").timeout(2 * 1000, 60 * 1000).asString
    if (resp.isError) {
      None
    }
    else {
      Some(resp.body.lines.map(s => Paths.get(s)).toSet)
    }
  }

  def compile(r: Res, distro: String): Expr = r match {
    case EnsureFile(p, CInline(c)) =>
      If(TestFileState(p, IsFile), Rm(p), Skip) >> CreateFile(p, c)
    case EnsureFile(p, CFile(s)) =>
      If(TestFileState(p, IsFile), Rm(p), Skip) >> Cp(s, p)
    case File(p, CInline(c), false) =>
      If(TestFileState(p, IsFile),
         Rm(p) >> CreateFile(p, c),
         If(TestFileState(p, DoesNotExist),
            CreateFile(p, c),
            Error))
    case File(p, CInline(c), true) =>
    // TODO(arjun): needs support for recursive directory removal and can simplify too
     If(Or (TestFileState(p, IsDir), TestFileState(p, IsFile)),
         Rm(p), Skip) >>
      CreateFile(p, c)
    case File(p, CFile(s), false) =>
      If(TestFileState(p, IsFile),
        Rm(p) >> Cp(s, p),
        If(TestFileState(p, DoesNotExist),
          Cp(s, p),
          Error))
    case File(p, CFile(s), true) =>
      If(Or(TestFileState(p, IsDir), TestFileState(p, IsFile)),
        Rm(p), Skip) >>
      Cp(s, p)
    case AbsentPath(p, false) =>
      // TODO(arjun): why doesn't this work for directories too?
      If(TestFileState(p, IsFile), Rm(p), Skip)
    case AbsentPath(p, true) =>
      // TODO(arjun): Can simplify the program below
      If(TestFileState(p, IsDir),
          Rm(p), // TODO(arjun): need to implement directory removal in fsmodel
          If(TestFileState(p, IsFile),
             Rm(p),
             Skip))
    case Directory(p) =>
      If(TestFileState(p, IsDir),
         Skip,
         If(TestFileState(p, IsFile),
            Rm(p) >> Mkdir(p),
            Mkdir(p)))
    case User(name, present, manageHome) => {
      val u = Paths.get(s"/etc/users/$name")
      val g = Paths.get(s"/etc/groups/$name")
      val h = Paths.get(s"/home/$name")
      present match {
        case true => {
          val homeCmd = if (manageHome) {
            If(TestFileState(h, DoesNotExist), Mkdir(h), Skip)
          }
          else {
            Skip
          }
          If(TestFileState(u, DoesNotExist), Mkdir(u), Skip) >>
          If(TestFileState(g, DoesNotExist), Mkdir(g), Skip) >>
          homeCmd
        }
        case false => {
          val homeCmd = if (manageHome) {
            If(TestFileState(h, DoesNotExist), Skip, Rm(h))
          }
          else {
            Skip
          }
          If(TestFileState(u, DoesNotExist), Skip, Rm(u)) >>
          If(TestFileState(g, DoesNotExist), Skip, Rm(g)) >>
          homeCmd
        }
      }
    }
    case Group(name, present) => {
      val p = s"/etc/groups/$name"
      present match {
        case true => If(TestFileState(p, DoesNotExist), Mkdir(p), Skip)
        case false => If(!TestFileState(p, DoesNotExist), Rm(p), Skip)
      }
    }
    case Package(name, true) => {

      val paths = queryPackage(distro, name).getOrElse(throw PackageNotFound(distro, name))
      val dirs = paths.map(_.ancestors()).reduce(_ union _) - root -- Set[Path]("/bin", "/usr", "/etc")
      val files = paths -- dirs

      val mkdirs = dirs.toSeq.sortBy(_.getNameCount)
        .map(d => If(TestFileState(d, IsDir), Skip, Mkdir(d)))

      val somecontent = ""
      val createfiles = files.toSeq.map((f) => CreateFile(f, somecontent))
      val exprs = mkdirs ++ createfiles

      If(TestFileState(s"/packages/${name}", DoesNotExist),
         Seq(CreateFile(s"/packages/${name}", ""), Block(exprs: _*)),
         Skip)
    }
    case Package(name, false) => {
      // TODO(arjun): Shouldn't this only remove files and newly created directories?
      val files =  queryPackage(distro, name).getOrElse(throw PackageNotFound(distro, name)).toList
      val exprs = files.map(f => If(TestFileState(f, DoesNotExist), Skip, Rm(f)))
      val pkgInstallInfoPath = s"/packages/$name"
      // Append at end
      If(TestFileState(pkgInstallInfoPath, DoesNotExist),
          Skip,
          Block((Rm(pkgInstallInfoPath) :: exprs) :_*))
    }
    case self@SshAuthorizedKey(_, present, _, key) => {
      val p = self.keyPath
      present match {
        case true => {
          If(TestFileState(p, IsFile), Rm(p), Skip) >> CreateFile(p, key)
        }
        case false => {
          If(TestFileState(p, IsFile), Rm(p), Skip)
        }
      }
    }
    case self@Service(name) => If(TestFileState(self.path, IsFile), Skip, Error)
    case Notify => Skip
    case _ => throw NotImplemented(r.toString)
  }

}
