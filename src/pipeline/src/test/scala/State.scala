package pipeline

object Ubuntu {

  import java.nio.file.Paths
  import java.nio.file.Path
  import scala.io.Source._
  import scala.collection.immutable.HashMap

  import fsmodel.core._
  import Eval._

  import scala.language.implicitConversions
  implicit def toPathState(elem: (String, FileState)) = (Paths.get(elem._1), elem._2)

  /*
   * Initial state of a generic ubuntu filesystem
   * Source: https://help.ubuntu.com/community/LinuxFilesystemTreeOverview
   */
  val lightweight_fs: State = Map(paths.root -> IsDir,
                            "/bin" -> IsDir,
                            "/boot" -> IsDir,
                            "/dev/" -> IsDir,
                            "/etc/" -> IsDir,
                            "/etc/users/" -> IsDir, // non-standard
                            "/etc/groups/" -> IsDir, // non-standard
                            "/home/" -> IsDir,
                            "/lib/" -> IsDir,
                            "/media/" -> IsDir,
                            "/mnt/" -> IsDir,
                            "/opt/" -> IsDir,
                            "/proc/" -> IsDir,
                            "/root/" -> IsDir,
                            "/sbin/" -> IsDir,
                            "/srv/" -> IsDir,
                            "/sys/" -> IsDir,
                            "/tmp/" -> IsDir,
                            "/usr/" -> IsDir,
                            "/usr/bin/" -> IsDir,
                            "/usr/lib/" -> IsDir,
                            "/var/" -> IsDir,
                            "/var/log/" -> IsDir)

  def tagToFileState(tag: String): FileState = tag match {
    case "d" => IsDir
    case "f" => IsFile
    case "l" => IsFile // TODO(nimish): Links not supported, treated as files
    case _ => throw new Exception(s"Unknown tag: ${tag}")
  }

  lazy val fs: HashMap[Path, FileState] = {
    val file = fromURL(getClass.getResource("/ubuntu.fs"))
    val entries = (for (line <- file.getLines()) yield {
      val Array(path, tag) = line.split(" ")
      (Paths.get(path), tagToFileState(tag))
    })
    HashMap() + ("/etc/users/" -> IsDir,
                 "/etc/groups/" -> IsDir,
                 entries.toSeq: _*)
  }
}
