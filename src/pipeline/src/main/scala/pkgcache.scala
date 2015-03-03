package pipeline

import java.io.File
import java.nio.file.{Path, Paths, Files}
import java.nio.charset.StandardCharsets

import puppet.common.util._

import scala.util.Try

/* Disk based cache to speed up apt-file */
private[pipeline] class PackageCache(cacheroot: Path) {

  val root = cacheroot.normalize().toAbsolutePath()
  require(Files.exists(root) && Files.isDirectory(root))

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
