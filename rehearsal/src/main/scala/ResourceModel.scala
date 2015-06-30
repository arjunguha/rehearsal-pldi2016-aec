package rehearsal

object ResourceModel {

  import ResourceToExpr.pkgcache

  import java.nio.file.{Path, Paths}
  import scala.collection.immutable.Set
  import FSSyntax._
  import rehearsal.Implicits._

  sealed trait Res {
    def compile(): Expr = ResourceModel.compile(this)
  }

  case class File(path: Path, content: String, force: Boolean) extends Res
  case class EnsureFile(path: Path, content: String) extends Res
  case class AbsentPath(path: Path, force: Boolean) extends Res
  case class Directory(path: Path) extends Res
  case class Package(name: String, present: Boolean) extends Res
  case class Group(name: String, present: Boolean) extends Res
  case class User(name: String, present: Boolean, manageHome: Boolean) extends Res

  case class SshAuthorizedKey(user: String, present: Boolean, name: String, key: String) extends Res {
    val keyPath = s"/home/$user/.ssh/$name"
  }


  def compile(r: Res): Expr = r match {
    case EnsureFile(p, c) =>
      If(TestFileState(p, IsFile), Rm(p), Skip) >> CreateFile(p, c)
    case File(p, c, false) =>
      If(TestFileState(p, IsFile),
         Rm(p) >> CreateFile(p, c),
         If(TestFileState(p, DoesNotExist),
            CreateFile(p, c),
            Skip))
    case File(p, c, true) =>
    // TODO(arjun): needs support for recursive directory removal and can simplify too
     If(TestFileState(p, IsDir),
         Rm(p),
         If(TestFileState(p, IsFile), Rm(p), Skip)) >>
      CreateFile(p, c)
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
            If(TestFileState(h, IsDir), Rm(h), Skip)
          }
          else {
            Skip
          }
          If(TestFileState(u, IsDir), Rm(u), Skip) >>
          If(TestFileState(g, IsDir), Rm(g), Skip) >>
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
      val files = pkgcache.files(name).getOrElse(Set())
      val dirs = allpaths(files) -- files - root

      val mkdirs = dirs.toSeq.sortBy(_.getNameCount)
        .map(d => If(TestFileState(d, DoesNotExist),
                     Mkdir(d),
                     Skip))

      val somecontent = ""
      val createfiles = files.toSeq.map((f) => CreateFile(f, somecontent))
      val exprs = mkdirs ++ createfiles :+ CreateFile(s"/packages/$name", "")

      If(TestFileState(s"/packages/${name}", DoesNotExist),
         Block(exprs: _*),
         Skip)
    }
    case Package(name, false) => {
      val files = pkgcache.files(name).getOrElse(Set()).toList
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
        case true => If(Not(TestFileState(p, DoesNotExist)), Rm(p), Skip) >> CreateFile(p, key)
        case false => If(Not(TestFileState(p, DoesNotExist)), Rm(p), Skip)
      }
    }
    case _ => throw NotImplemented(r.toString)
  }

}
