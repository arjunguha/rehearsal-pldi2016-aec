package eval

object Implicits {

  import  scala.language.implicitConversions
  import java.nio.file.{Path, Paths, Files}
  import scalax.collection.Graph
  import scalax.collection.GraphEdge.DiEdge

  implicit def stringToPath(str: String): Path = Paths.get(str)

  implicit class RichString(str: String) {

    def toPath = Paths.get(str)
  }

  implicit def MapToPerfMap(map: Map[Path, FileState]): PerfMap[Path, FileState] = {
    PerfMap(map)
  }

  implicit class RichExpr(e1: Expr) {

    def +(e2: Expr) = (e1, e2) match {
      case (Error, _) => e2
      case (_, Error) => e1
      case _ if e1 == e2 => e1
      case _ => Alt(e1, e2)
    }

    def *(e2: Expr) = (e1, e2) match {
      case (Error, _ ) => Error
      case (_, Error) => Error
      case (_, Skip) => e1
      case (Skip, _) => e2
      case _ => Concur(e1, e2)
    }

    def >>(e2: Expr) = (e1, e2) match {
      case (Skip, _) => e2
      case (_, Skip) => e1
      case (Error, _) => Error
      case (_, Error) => Error
      case _ => Seq(e1, e2)
    }
  }

  implicit class RichGraph(g: Graph[Ample.Node, DiEdge]) {

    def saveDotFile(path: Path): Unit = {
      import scalax.collection.io.dot._
      import scala.language.existentials

      val root = DotRootGraph(directed=true, id=Some("Program"))

      def edgeT(edge : Graph[Ample.Node, DiEdge]#EdgeT) = {
        val e = DotEdgeStmt(edge.edge.from.toString, edge.edge.to.toString, Nil)
        Some(root, e)
      }

      def nodeT(node: Graph[Ample.Node, DiEdge]#NodeT) = {
        Some(root, DotNodeStmt(node.toString, Nil))
      }

      val dot = g.toDot(root, edgeT, None, None, Some(nodeT))
      Files.write(path, dot.toString.getBytes)
    }

  }


}
