package object rehearsal {

  import scala.reflect.runtime.universe.TypeTag
  import scalax.collection.GraphPredef._
  import scalax.collection.Graph
  import scalax.collection.GraphEdge.DiEdge
  import java.nio.file.{Paths, Path, Files}
  import scala.annotation.tailrec
  import FSSyntax._
  import scalax.collection.edge.Implicits._
  import rehearsal.Implicits._
  import scala.util.{Try, Success, Failure}

  def topologicalSort[V](graph: scalax.collection.Graph[V, DiEdge]): List[V] = {
    if (graph.isEmpty) {
      List()
    }
    else {
      graph.nodes.find(_.inDegree == 0) match {
        case None => throw CannotUpdate("cyclic graph")
        case Some(node) => {
          node :: topologicalSort(graph - node)
        }
      }
    }
  }

  def unions[A](sets: scala.Seq[Set[A]]): Set[A] = sets.foldLeft(Set[A]()) (_ union _)

  val root = Paths.get("/")

  // returns all paths along with their ancestors
  def allpaths(pathSet: Set[Path]): Set[Path] = {
    @tailrec
    def loop(p: Path, result: Set[Path]): Set[Path] = {
      // Check if we have already solved this problem
      if (!result(p)) {
        p.getParent match {
          case null => result + p.normalize
          case parent: Path => loop(parent, result + p.normalize)
        }
      }
      else {
        result
      }
    }

    pathSet.foldLeft(Set.empty[Path]) { (pathSet, path) => loop(path, pathSet) }
  }

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
