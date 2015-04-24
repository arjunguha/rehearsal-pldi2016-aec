package eval

object Implicits {

  import  scala.language.implicitConversions
  import java.nio.file.{Path, Paths, Files}
  import scalax.collection.Graph
  import scalax.collection.edge.LDiEdge
  import scalax.collection.GraphEdge.DiEdge
  import java.security.MessageDigest

  implicit def stringToPath(str: String): Path = Paths.get(str)

  implicit def contentToHash(content: String): Array[Byte] =
    MessageDigest.getInstance("MD5").digest(content.getBytes)

  implicit class RichString(str: String) {

    def toPath = Paths.get(str)
  }

  implicit def MapToPerfMap(map: Map[Path, FileState]): PerfMap[Path, FileState] = {
    PerfMap(map)
  }

  implicit class RichPred(a: Pred) {

    def &&(b: Pred): Pred = And(a, b)
    def ||(b: Pred): Pred = Or(a, b)
    def unary_!(): Pred = Not(a)
  }

  implicit class RichExpr(e1: Expr) {

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

      // Converts to PDF if the dot tool is installed.
      if (Files.isRegularFile(Paths.get("/usr/bin/dot"))) {
        import scala.sys.process._
        val pdf = path.resolveSibling(s"${path.getFileName}.pdf")
        val proc = scala.collection.Seq("/usr/bin/dot", "-Tpdf", path.toString) #> pdf.toFile
        assert (proc.! == 0)
      }
    }
  }

  implicit class RichAmpleGraph(g: Graph[AmpleGraph.Node, LDiEdge]) {

    def saveDotFile(path: Path): Unit = {
      import scalax.collection.io.dot._
      import scala.language.existentials

      val root = DotRootGraph(directed=true, id=Some("Program"))

      def edgeT(edge : Graph[AmpleGraph.Node, LDiEdge]#EdgeT) = {
        val label = List(DotAttr("label", edge.edge.label.toString))
        val e = DotEdgeStmt(edge.edge.from.hashCode.toString, edge.edge.to.hashCode.toString, label)
        Some(root, e)
      }

      val dot = g.toDot(root, edgeT)
      Files.write(path, dot.toString.getBytes)

      // Converts to PDF if the dot tool is installed.
      if (Files.isRegularFile(Paths.get("/usr/bin/dot"))) {
        import scala.sys.process._
        val pdf = path.resolveSibling(s"${path.getFileName}.pdf")
        val proc = scala.collection.Seq("/usr/bin/dot", "-Tpdf", path.toString) #> pdf.toFile
        assert (proc.! == 0)
      }
    }
  }
}
