import puppet.Modules
import puppet.graph.Resource
import puppet.syntax.{TopLevel, parse}
import scala.util.{Try, Success, Failure}
import java.nio.file.{Files, Paths, Path}

class GithubSuite extends org.scalatest.FunSuite {

  val env = puppet.Facter.fromFile("rehearsal/src/test/arjun-vm.facter") getOrElse
    (throw new Exception("Facter environment not found"))

  def dirListing(p: Path): Seq[Path] = {
    import scala.collection.JavaConversions._
    val stream = Files.newDirectoryStream(p)
    val lst = stream.toList.toSeq
    stream.close
    lst
  }

  def recursiveDirListing(p: Path): Seq[Path] = {
    dirListing(p).flatMap { child =>
      if (Files.isDirectory(child)) { dirListing(child) }
      else { Seq(child) }
    }
  }

  def findPuppetFiles(repo: Path): Option[(Path, TopLevel)] = {
    val ppFiles = recursiveDirListing(repo).filter(_.getFileName.toString.endsWith(".pp")).toList
    if (ppFiles.length == 0) {
      None
    }
    else {
      Try(ppFiles.map(p => parse(new String(Files.readAllBytes(p))))) match {
        case Success(topLevels) => Some(repo -> TopLevel(topLevels.map(_.items).flatten))
        case Failure(_) => None
      }
    }
  }


  val repos = dirListing(Paths.get("benchmarks/github"))
    .filter(p => Files.isDirectory(p))
    .flatMap(user => dirListing(user))
    .map(findPuppetFiles)
    .flatten

  for ((repo, topLevel) <- repos) {

    Try(topLevel.desugar.toGraph(env).head._2) match {
      case Failure(_) => ()
      case Success(g) => {
        val files = g.nodes.filter(_.typ == "File")
        val numFiles = files.size
        val fileDeps = files.map(_.inDegree).sum
        val numNodes = g.nodes.size
        println(s"$repo, $numFiles, $fileDeps, $numNodes")
      }
    }
  }

}
