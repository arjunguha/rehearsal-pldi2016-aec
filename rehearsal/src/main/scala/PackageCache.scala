package rehearsal

/* Disk based cache to speed up apt-file */
class PackageCache(cacheroot: java.nio.file.Path) extends com.typesafe.scalalogging.LazyLogging {

  import rehearsal._
  import java.io.File
  import java.nio.file.{Path, Paths, Files}
  import java.nio.charset.StandardCharsets
  import scala.util.Try

  val root = cacheroot.normalize().toAbsolutePath()
  require(Files.exists(root) && Files.isDirectory(root),
          s"Directory ${root} missing")

  val newline = sys.props("line.separator")

  def write(pkg: String, files: Set[Path]) {
    assert(files.size > 0)
    val cachepath = s"${root}/${pkg}"
    val txt = files.map(_.toString + newline).reduce(_ + _)
    Files.write(Paths.get(cachepath), txt.getBytes(StandardCharsets.UTF_8))
  }

  def read(pkg: String): Option[Set[Path]] = {
    val cachepath = s"${root}/${pkg}"
    Try(scala.io.Source.fromFile(cachepath).getLines
                       .map((p) => Paths.get(p)).toSet).toOption
  }

  def aptfile(pkg: String): Option[Set[Path]] = {
    val cmd = s"apt-file -F list $pkg"
    logger.info("Running $cmd")
    val (sts, out, err) = Cmd.exec(cmd)
    if (0 == sts && out.lines.size > 0) {
      Some(out.lines.toList.map((l) => Paths.get(l.split(" ")(1))).toSet)
    }
    else None
  }

  def files(pkg: String): Option[Set[Path]] = {
    read(pkg) orElse {
      val ofiles = aptfile(pkg)
      ofiles.foreach((files) => write(pkg, files))
      ofiles
    }
  }

  def clear() {
    for(file <- (new File(root.toString)).listFiles.filter(_.isFile)) {
      Files.deleteIfExists(file.toPath())
    }
  }

  def entryExists(pkg: String): Boolean = {
    val cachepath = s"${root}/${pkg}"
    Files.exists(Paths.get(cachepath))
  }
}

object PackageCache {

  import java.nio.file._

  def apply(): PackageCache = {
    val benchmarksDir = Paths.get("benchmarks")
    if (!Files.isDirectory(benchmarksDir)) {
      Files.createDirectory(benchmarksDir)
    }
    val pkgcacheDir = benchmarksDir.resolve("pkgcache")
    if (!Files.isDirectory(pkgcacheDir)) {
      Files.createDirectory(pkgcacheDir)
    }
    new PackageCache(pkgcacheDir)
  }

}
