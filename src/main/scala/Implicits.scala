package rehearsal

trait Extractor[A,B] {
  def apply(from: A): Option[B]
}

object Implicits {

  import scala.language.implicitConversions
  import scalax.collection.Graph
  import scalax.collection.GraphEdge.DiEdge
  import java.nio.file.{Path, Paths, Files}

  implicit def stringToPath(str: String): Path = Paths.get(str)

  implicit class RichString(str: String) {

    def toPath = Paths.get(str)
  }

  implicit def extractString = new Extractor[PuppetSyntax.Expr, String] {
    import PuppetSyntax._

    def apply(e: Expr) = e match {
      case EStr(s) => Some(s)
      case _ => None
    }
  }

  implicit def extractBool = new Extractor[PuppetSyntax.Expr, Boolean] {
    import PuppetSyntax._

    def apply(e: Expr) = e match {
      case EStr("yes") => Some(true)
      case EStr("no") => Some(false)
      case EBool(b) => Some(b)
      case _ => None
    }
  }

  implicit class RichDiGraph[V](graph: Graph[V, DiEdge]) {

    def topologicalSort(): List[V] = {
      if (graph.isEmpty) {
        List()
      }
      else {
        graph.nodes.find(_.inDegree == 0) match {
          case None => throw new IllegalArgumentException("cannot topologically sort a cyclic graph")
          case Some(node) => node :: (graph - node).topologicalSort()
        }
      }
    }

  }

  implicit class RichPath(path: Path) {

    def ancestors(): Set[Path] = {
      def loop(p: Path, set: Set[Path]): Set[Path] = {
        if (p == null) {
          set
        }
        else {
          loop(p.getParent(), set + p)
        }
      }
      loop(path.getParent(), Set())
    }

  }

}
