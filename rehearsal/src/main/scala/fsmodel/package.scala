package rehearsal

package object fsmodel {

  import scalax.collection.Graph
  import scalax.collection.GraphEdge.DiEdge
  import java.nio.file.{Paths, Path}
  import scala.annotation.tailrec
  import FSSyntax._


  type FileScriptGraph = Graph[Expr, DiEdge]

  val root = Paths.get("/")

  // returns all paths along with their ancestors
  def allpaths(pathSet: Set[Path]): Set[Path] = {
    @tailrec
    def loop(p: Path, result: Set[Path]): Set[Path] = {
      // Check if we have already solved this problem
      if (!result(p)) {
        p.getParent match {
          case null => result
          case parent: Path => loop(parent, result + p.normalize)
        }
      }
      else {
        result
      }
    }

    pathSet.foldLeft(Set.empty[Path]) { (pathSet, path) => loop(path, pathSet) }
  }

}