package cook.fingerprint

import plasma.docker._
import java.nio.file
import java.io._
import org.apache.commons._ 
import scala.concurrent._
import scala.async.Async.{async, await}

object FingerPrint {

  val aufs_root = "/var/lib/docker/aufs/diff"

  private def toLocalPath(dockerPath: String, containerId: String): String = 
    "%s/%s%s".format(aufs_root, containerId, dockerPath)

  private def digestFile (f: String): String = {
    val fis = new FileInputStream(new File(f));
    val md5 = codec.digest.DigestUtils.md5Hex(fis);
    fis.close()
    md5
  }

  /* fingerprint is map of files created/modified by command and 
   * their corresponding md5 sums
   */
  def apply(docker_url: String,
            cmd: String)
    (implicit ec: ExecutionContext): Future[Map[String, String]] = async {
    val docker = new Docker(docker_url)
    val cfg = ContainerConfig("ubuntu", "", "", 0, 0, false, true, true, false, false,
                              List[String](), "", List[String](), cmd.split(' ').toList,
                              false, false, Map("/tmp" -> None), "", Map("22/tcp" -> None))
    await (for {
      containerRef <- docker.createContainer(cfg)
      fp <- for {
        _ <- docker.startContainer(containerRef.Id)
        _ <- docker.waitContainer(containerRef.Id)
        chgs <- docker.containerFileSystemChanges(containerRef.Id)
      } yield chgs.map({case ch if ch.Kind == 0 || ch.Kind == 1 => ch.Path}) // Filter only file creation and change events
                  .filterNot(_.startsWith("/dev/")) // hack for excluding immediately apparent special files
                  .filterNot(f => {
                    val file = new File(toLocalPath(f, containerRef.Id))
                    !file.exists || file.isDirectory
                  }) // Exclude Directories
                  .map(f => (f, digestFile(toLocalPath(f,containerRef.Id))))
                  .toMap
      _ <- docker.deleteContainer(containerRef.Id)
    } yield fp)
  }
}
