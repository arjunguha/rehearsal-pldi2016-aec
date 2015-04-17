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

  implicit class RichPred(a: Pred) {

    def nnf(): Pred = a match {
      case Not(And(a, b)) => Or(Not(a).nnf(), Not(b).nnf())
      case Not(Or(a, b)) => And(Not(a).nnf(), Not(b).nnf())
      case Not(Not(a)) => a.nnf()
      case And(a, b) => And(a.nnf(), b.nnf())
      case Or(a, b) => Or(a.nnf(), b.nnf())
      case Not(a) => Not(a.nnf())
      case _ => a
    }

    def cnf(): Pred = a.nnf() match {
      case Or(a, And(b, c)) => And(Or(a, b), Or(a, c)).cnf()
      case Or(And(b, c), a) => And(Or(b, a), Or(c, a)).cnf()
      case And(a, b) => And(a.cnf(), b.cnf())
      case Or(a, b) => Or(a.cnf(), b.cnf())
      case Not(a) => Not(a.cnf())
      case _ => a
    }
    
    def &&(b: Pred): Pred = And(a, b)
    def ||(b: Pred): Pred = Or(a, b)
    def unary_!(): Pred = Not(a)
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
