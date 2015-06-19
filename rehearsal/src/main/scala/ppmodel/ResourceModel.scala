package rehearsal.ppmodel

object ResourceModel {

  import ResourceToExpr.pkgcache

  import java.nio.file.{FileSystems, Path, Paths}
  import scala.collection.immutable.Set
  import exp.{External => E, CommonSyntax => C}
  import rehearsal._
  import rehearsal.fsmodel._
  import rehearsal.fsmodel.Implicits._

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
            If(TestFileState(h, DoesNotExist), Mkdir(u), Skip)
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
    case _ => throw NotImplemented(r.toString)
  }

  def coerce(r: Res): E.Expr = r match {
    case File(path, hash, force) => E.EConstr("RFile", List(E.EConstr(path.toString, Nil), E.EConstr(hash, Nil), E.EConst(E.CBool(force))))
    case EnsureFile(path, hash) => E.EConstr("REnsureFile", List(E.EConstr(path.toString, Nil), E.EConstr(hash, Nil)))
    case AbsentPath(path, force) => E.EConstr("RAbsentPath", List(E.EConstr(path.toString, Nil), E.EConst(E.CBool(force))))
    case Directory(path) => E.EConstr("RDirectory", List(E.EConstr(path.toString, Nil)))
    case _ => throw NotImplemented(r.toString)
  }

  def coerceAll(r: List[Res]): E.Expr = {
    r.map(coerce).foldRight[E.Expr](E.EConstr("RListNil", Nil))({ case (hd, tl) => E.EConstr("RListCons", List(hd, tl)) })
  }

  def allPaths(path: Path): List[Path] = Stream.iterate(path)(_.getParent).takeWhile(_ != null).toList
  def toAdd(path: Path): List[(String, List[E.Type])] = allPaths(path).map(_.toString).zip(Stream.continually(Nil))

  import E.TypeDef
  type Constr = Set[(String, List[E.Type])]
  def buildTypes(r: List[Res]): (TypeDef, TypeDef) = r.foldLeft[(Constr, Constr)]((Set(), Set())) {
    case ((pathDef, hashDef), File(path, hash, _)) => (pathDef ++ toAdd(path), hashDef + ((hash, Nil)))
    case ((pathDef, hashDef), EnsureFile(path, hash)) => (pathDef ++ toAdd(path), hashDef + ((hash, Nil)))
    case ((pathDef, hashDef), AbsentPath(path, _)) => (pathDef ++ toAdd(path), hashDef)
    case ((pathDef, hashDef), Directory(path)) => (pathDef ++ toAdd(path), hashDef)
    case (_, r) => throw NotImplemented(r.toString)
  } match {
    case (pathDef, hashDef) => (TypeDef("path", pathDef.toList), TypeDef("hash", hashDef.toList))
  }

  def getParent(path: String): Option[String] = {
    val parent = FileSystems.getDefault.getPath(path).getParent
    if (parent == null) {
      None
    } else {
      Some(parent.toString)
    }
  }

  def genGetParent(pathDef: TypeDef): E.Expr = {
    val cases = pathDef.cons.map(_._1).map { p =>
      (E.PConstr(p, Nil),
       getParent(p) match {
         case Some(str) => E.EConstr("Parent", List(E.EConstr(str, Nil)))
         case None =>  E.EConstr("NoParent", Nil)
       })
    }
    E.TypedFun(C.Id("path"), E.TConstructor("path"), E.EMatch(E.EId(C.Id("path")), cases))
  }

  private def matchesPath(p: Path, r: Res): Boolean = r match {
    case File(p2, _, _) => p == p2
    case EnsureFile(p2, _) => p == p2
    case AbsentPath(p2, _) => p == p2
    case Directory(p2) => p == p2
    case _ => false
  }

  type SSeq[A] = scala.Seq[A]
  private def update(delta: SSeq[Res], p: Path, rs: SSeq[Res]): SSeq[Res] = rs.find(matchesPath(p, _)) match {
    case Some(f@File(_, _, _)) => delta :+ f
    case Some(f@EnsureFile(_, _)) => delta :+ f
    case Some(a@AbsentPath(_, _)) => delta :+ a
    case Some(d@Directory(_)) => delta :+ d
    case Some(r) => throw NotImplemented(r.toString)
    case None => delta :+ AbsentPath(p, false)
  }

  def getDelta(r1: SSeq[Res], r2: SSeq[Res]): SSeq[Res] = r1.foldLeft[SSeq[Res]](scala.Seq()) {
    case (delta, res) if r2.contains(res) => delta
    case (delta, res) => res match {
      case File(path, _, _) => update(delta, path, r2)
      case EnsureFile(path, _) => update(delta, path, r2)
      case AbsentPath(path, _) => update(delta, path, r2)
      case Directory(path) => update(delta, path, r2)
      case _ => delta
    }
  }
}
