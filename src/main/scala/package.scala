package object rehearsal {

  import java.nio.file.{Paths, Path, Files}
  import rehearsal.Implicits._

  val root = Paths.get("/")

  def dirListing(p: Path): scala.Seq[Path] = {
    import scala.collection.JavaConversions._
    val stream = Files.newDirectoryStream(p)
    val lst = stream.toList.toSeq
    stream.close
    lst
  }

  def recursiveDirListing(p: Path): scala.Seq[Path] = {
    dirListing(p).flatMap { child =>
      if (Files.isDirectory(child)) { recursiveDirListing(child) }
      else { scala.Seq(child) }
    }
  }

  def time[A](thunk: => A): (A, Long) = {
    val start = System.currentTimeMillis
    val r = thunk
    val duration = System.currentTimeMillis - start
    r -> duration
  }


}
