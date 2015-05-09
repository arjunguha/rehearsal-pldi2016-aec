package pipeline

import puppet.common.resource._
import puppet.common.util._
import eval._
import eval.Implicits._

private[pipeline] object PostCondition {
  import java.nio.file.{Files, Paths}

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
      case _ => throw new Exception(s"ensure attribute missing for file ${r.name}")
    }
  }

  def PuppetPackage(r: Resource): Pred = {
    val validEnsureVals = List("present", "installed", "absent", "purged", "held", "latest")
    
    val ensure = validVal(r, "ensure", validEnsureVals) getOrElse "installed"
    val provider = r.get[String]("provider")

    if(provider.isDefined && provider.get != "apt") {
      throw new Exception(s"""package(${r.name}): "${provider.get}" provider not supported""")
    }

    ensure match {
      case "present" | "installed" | "latest" => {
        val files = pkgcache.files(r.name) getOrElse
          (throw new Exception(s"Package not found: ${r.name}"))

        val allpaths = paths.allpaths(files)

        val dirs = (allpaths -- files)
        
        val dirPreds = dirs.toSeq.map(TestFileState(_, IsDir))
        val filePreds = files.toSeq.map(TestFileState(_, IsFile))
        val preds = dirPreds ++ filePreds

        And(preds: _*)
      }

      case "absent" | "purged" => {
        val files = pkgcache.files(r.name) getOrElse
          (throw new Exception(s"Package not found: ${r.name}"))

        And(files.toSeq.map(TestFileState(_, DoesNotExist)): _*)
      }

      case "held"   => throw new Exception("NYI package held") // TODO
      case _ => throw new Exception(s"Invalid value for ensure: ${ensure}")
    }
  }


  def apply(r: Resource): Pred = r.typ match {
    case "File" => File(r)
    case "Package" => PuppetPackage(r)
    case _ => throw new Exception("Resource type \"%s\" not supported yet".format(r.typ))
  } 
}
