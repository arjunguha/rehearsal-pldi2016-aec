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
      ite(testFileState(p, IsFile), rm(p), Skip) >> createFile(p, c)
    case EnsureFile(p, CFile(s)) =>
      ite(testFileState(p, IsFile), rm(p), Skip) >> cp(s, p)
    case File(p, CInline(c), false) =>
      ite(testFileState(p, IsFile),
         rm(p) >> createFile(p, c),
         ite(testFileState(p, DoesNotExist),
            createFile(p, c),
            Error))
    case File(p, CInline(c), true) =>
    // TODO(arjun): needs support for recursive directory removal and can simplify too
     ite(testFileState(p, IsDir) || testFileState(p, IsFile),
         rm(p), Skip) >>
      createFile(p, c)
    case File(p, CFile(s), false) =>
      ite(testFileState(p, IsFile),
        rm(p) >> cp(s, p),
        ite(testFileState(p, DoesNotExist),
          cp(s, p),
          Error))
    case File(p, CFile(s), true) =>
      ite(testFileState(p, IsDir) || testFileState(p, IsFile),
        rm(p), Skip) >>
      cp(s, p)
    case AbsentPath(p, false) =>
      // TODO(arjun): why doesn't this work for directories too?
      ite(testFileState(p, IsFile), rm(p), Skip)
    case AbsentPath(p, true) =>
      // TODO(arjun): Can simplify the program below
      ite(testFileState(p, IsDir),
          rm(p), // TODO(arjun): need to implement directory removal in fsmodel
          ite(testFileState(p, IsFile),
             rm(p),
             Skip))
    case Directory(p) =>
      ite(testFileState(p, IsDir),
         Skip,
         ite(testFileState(p, IsFile),
            rm(p) >> mkdir(p),
            mkdir(p)))
    case User(name, present, manageHome) => {
      val u = Paths.get(s"/etc/users/$name")
      val g = Paths.get(s"/etc/groups/$name")
      val h = Paths.get(s"/home/$name")
      present match {
        case true => {
          val homeCmd = if (manageHome) {
            ite(testFileState(h, DoesNotExist), mkdir(h), Skip)
          }
          else {
            Skip
          }
          ite(testFileState(u, DoesNotExist), mkdir(u), Skip) >>
          ite(testFileState(g, DoesNotExist), mkdir(g), Skip) >>
          homeCmd
        }
        case false => {
          val homeCmd = if (manageHome) {
            ite(testFileState(h, DoesNotExist), Skip, rm(h))
          }
          else {
            Skip
          }
          ite(testFileState(u, DoesNotExist), Skip, rm(u)) >>
          ite(testFileState(g, DoesNotExist), Skip, rm(g)) >>
          homeCmd
        }
      }
    }
    case Group(name, present) => {
      val p = s"/etc/groups/$name"
      present match {
        case true => ite(testFileState(p, DoesNotExist), mkdir(p), Skip)
        case false => ite(!testFileState(p, DoesNotExist), rm(p), Skip)
      }
    }
    case Package(name, true) => {

      val paths = queryPackage(distro, name).getOrElse(throw PackageNotFound(distro, name))
      val dirs = paths.map(_.ancestors()).reduce(_ union _) - root -- Set[Path]("/bin", "/usr", "/etc")
      val files = paths -- dirs

      val mkdirs = dirs.toSeq.sortBy(_.getNameCount)
        .map(d => ite(testFileState(d, IsDir), Skip, mkdir(d)))

      val somecontent = ""
      val createfiles = files.toSeq.map((f) => createFile(f, somecontent))
      val exprs = mkdirs ++ createfiles

      ite(testFileState(s"/packages/${name}", DoesNotExist),
         createFile(s"/packages/${name}", "") >> Block(exprs: _*),
         Skip)
    }
    case Package(name, false) => {
      // TODO(arjun): Shouldn't this only remove files and newly created directories?
      val files =  queryPackage(distro, name).getOrElse(throw PackageNotFound(distro, name)).toList
      val exprs = files.map(f => ite(testFileState(f, DoesNotExist), Skip, rm(f)))
      val pkgInstallInfoPath = s"/packages/$name"
      // Append at end
      ite(testFileState(pkgInstallInfoPath, DoesNotExist),
          Skip,
          Block((rm(pkgInstallInfoPath) :: exprs) :_*))
    }
    case self@SshAuthorizedKey(_, present, _, key) => {
      val p = self.keyPath
      present match {
        case true => {
          ite(testFileState(p, IsFile), rm(p), Skip) >> createFile(p, key)
        }
        case false => {
          ite(testFileState(p, IsFile), rm(p), Skip)
        }
      }
    }
    case self@Service(name) => ite(testFileState(self.path, IsFile), Skip, Error)
    case Notify => Skip
    case _ => ???
  }

}
