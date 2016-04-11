package rehearsal

trait Extractor[A,B] {
  def apply(from: A): Option[B]
}

object Implicits {

  import scala.language.implicitConversions
  import scalax.collection.Graph
  import scalax.collection.GraphEdge.DiEdge
  import java.nio.file.{Paths, Files}

  implicit def stringToPath(str: String): Path = Paths.get(str)

  implicit class RichString(str: String) {

    def toPath = Paths.get(str)
  }

  implicit def extractString = new Extractor[PuppetSyntax.Expr, String] {
    import PuppetSyntax._

    def apply(e: Expr) = e match {
      case EStr(s) => Some(s)
      case ENum(n) => Some(n.toString)
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

  implicit class RichList[A](alist: List[A]) {

    def spanRight(pred: A => Boolean) = {
      val (suffixRev, prefixRev) = alist.reverse.span(pred)
      (prefixRev.reverse, suffixRev.reverse)
    }
  }

  implicit class RichDiGraph[V](graph: Graph[V, DiEdge]) {

    def topoSort(): List[Graph[V, DiEdge]#NodeT] = {
      if (graph.isEmpty) {
        Nil
      }
      else {
        graph.nodes.find(_.inDegree == 0) match {
          case None => throw new IllegalArgumentException("cannot topologically sort a cyclic graph")
          case Some(node) => node :: (graph - node).topoSort()
        }
      }
    }

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

    def shrink(node: Graph[V, DiEdge]#NodeT): Graph[V, DiEdge] = {
      val pairs = for (x <- node.diPredecessors;
                       y <- node.diSuccessors) yield DiEdge(x.value, y.value)

      graph ++ pairs - node
    }

    def ancestors(node: Graph[V, DiEdge]#NodeT): Set[Graph[V, DiEdge]#NodeT] = {
      def loop(fringe: List[Graph[V, DiEdge]#NodeT],
               result: Set[Graph[V, DiEdge]#NodeT]): Set[Graph[V, DiEdge]#NodeT] = fringe match {
        case Nil => result
        case head :: tail => {
          if (result.contains(head)) loop(tail, result)
          else loop(tail ++ head.diPredecessors, result + head)
        }
      }
      loop(List(node), Set()) - node
    }

    def descendants(node: Graph[V, DiEdge]#NodeT): Set[Graph[V, DiEdge]#NodeT] = {
      def loop(fringe: List[Graph[V, DiEdge]#NodeT],
               result: Set[Graph[V, DiEdge]#NodeT]): Set[Graph[V, DiEdge]#NodeT] = fringe match {
        case Nil => result
        case head :: tail => {
          if (result.contains(head)) loop(tail, result)
          else loop(tail ++ head.diSuccessors, result + head)
        }
      }
      loop(List(node), Set()) - node
    }

    def dotString(): String = {
      import scalax.collection.io.dot._

      val root = DotRootGraph(directed = true, id = Some("DirectedGraph"))

      // The types of the edge transformers are awful. Inlining them let's type inference figure them out.
      graph.toDot(root,
        innerEdge => Some(root, DotEdgeStmt(innerEdge.edge.from.toString,  innerEdge.edge.to.toString,  Nil)),
        None, None,
        Some(isolatedNode => Some(root, DotNodeStmt(isolatedNode.toString, Nil))))
    }

    def saveDotFile(p: Path): Unit = {
      import java.nio.file._
      val str = this.dotString()
      Files.write(p, str.getBytes)
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

  implicit class RichMap[A,B](self: Map[A, B]) {

    def combine[C, D](other: Map[A, C])(f: (Option[B], Option[C]) => Option[D]) = {
      val keys = self.keySet ++ other.keySet
      keys.foldLeft(Map[A,D]())({ case (map, k) =>
        f(self.get(k), other.get(k)) match {
          case None => map
          case Some(v) => map + (k -> v)
        }
      })
    }

    def mapIf(pred: A => Boolean, f: B => B): Map[A, B] = {
      def folder(acc: Map[A, B], k: A) = acc + (k -> f(acc(k)))
      self.keys.filter(pred).foldLeft(self)(folder)
    }

  }

}
