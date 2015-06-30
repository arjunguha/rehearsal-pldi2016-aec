package object rehearsal {

  import puppet.graph._
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
  import puppet.syntax.{TopLevel, parse}


  def toFileScriptGraph(resourceGraph: ResourceGraph): FileScriptGraph = {
    nodeMap((r: Resource) => ResourceToExpr(r), resourceGraph)
  }

  def nodeMap[A,B](f: A => B, inG: Graph[A, DiEdge])(implicit tag: TypeTag[B]): Graph[B, DiEdge] = {
    val nodeMap = inG.nodes.map(a => a -> f(a)).toMap
    val edges = inG.edges.map(edge => nodeMap(edge.from) ~> nodeMap(edge.to))
    Graph.from(nodeMap.values, edges)
  }

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

  def findPuppetFiles(repo: Path): Try[TopLevel] = {
    val ppFiles = recursiveDirListing(repo).filter(_.getFileName.toString.endsWith(".pp")).toList
    if (ppFiles.length == 0) {
      Failure(new RuntimeException("no Puppet files"))
    }
    else {
      Try(ppFiles.map(p => parse(new String(Files.readAllBytes(p))))) match {
        case Success(topLevels) => Success(TopLevel(topLevels.map(_.items).flatten))
        case Failure(exn) => Failure(exn)
      }
    }
  }


}
