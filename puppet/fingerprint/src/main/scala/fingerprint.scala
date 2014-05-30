package cook.fingerprint

import plasma.docker._
import java.nio.file
import java.io._
import org.apache.commons._ 
import scala.concurrent._
import scala.concurrent.duration._
import ExecutionContext.Implicits.global

object FingerPrint {

  val docker_root = "/var/lib/docker/aufs/diff/"

  import scala.collection.{mutable => mut}

  private def recursiveListFiles (f: File): Array[File] = {
    val these = f.listFiles
    these ++ these.filter (_.isDirectory).flatMap (recursiveListFiles)
  }

  private def digestfile (file: File): String = {
    val fis = new FileInputStream(file);
    val md5 = codec.digest.DigestUtils.md5Hex(fis);
    fis.close()
    md5
  }

  /* returns a map of files created/modified by command and 
   * their corresponding md5 sums
   */
  def apply(docker_url: String,
            cmd: String): mut.Map[String, String] = {
    val docker = new Docker(docker_url)
    val cfg = ContainerConfig("ubuntu", "", "", 0, 0, false, true, true, false, false,
                              List[String](), "", List[String](), cmd.split(' ').toList,
                              false, false, Map("/tmp" -> None), "", Map("22/tcp" -> None))
    val containerRef = Await.result(docker.createContainer(cfg), Duration.Inf)
    Await.result(docker.startContainer(containerRef.Id), Duration.Inf)
    Await.result(docker.waitContainer(containerRef.Id), Duration.Inf)
    // Container has stopped running now, check this might not be true in case of services
    // val fschanges = Await.result(docker.containerFileSystemChanges(containerRef.Id), Duration.Inf)
    // val files = filterFiles(fschanges.filter({ case ch if ch.Kind == 0 || ch.Kind == 1 => ch.Path))
    val files = recursiveListFiles (new File (docker_root + "/" + containerRef.Id)).filter(_.isFile)
    val fp = mut.Map[String, String]()
    files.map({case f => fp += (f.getPath -> digestfile(f))})
    Await.result(docker.deleteContainer(containerRef.Id), Duration.Inf)
    fp
  }
}
