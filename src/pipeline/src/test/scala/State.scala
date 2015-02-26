package pipeline

object Ubuntu {

  import java.nio.file.Paths

  import fsmodel.core._
  import Eval._

  import scala.language.implicitConversions
  implicit def toPathState(elem: (String, FileState)) = (Paths.get(elem._1), elem._2)

  /*
   * Initial state of a generic ubuntu filesystem
   * Source: https://help.ubuntu.com/community/LinuxFilesystemTreeOverview
   */
   // TODO:(nimish) add more paths like apt standard directories and files etc
  val fs_state: State = Map(paths.root -> IsDir,
                            "/bin" -> IsDir,
                            "/boot" -> IsDir,
                            "/dev/" -> IsDir,
                            "/etc/" -> IsDir,
                            "/etc/users/" -> IsDir,
                            "/etc/groups/" -> IsDir,
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
}
