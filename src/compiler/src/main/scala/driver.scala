package puppet.driver

import puppet.parser._
import puppet.core._
import puppet.core.eval._

// import puppet.runtime.core._

import scalax.collection.Graph
import scalax.collection.GraphEdge._
import scalax.collection.GraphPredef._

import puppet.common.{resource => resrc}

object PuppetDriver {

  import java.nio.file.{Files, Paths, Path}
  import java.io.File

  private def recursiveListFiles(f: File): Array[File] = {
    val these = f.listFiles
    these ++ these.filter(_.isDirectory).flatMap(recursiveListFiles)
  }

  private def manifestsInDirectory(dir: Path): List[Path] = {
    recursiveListFiles(dir.toFile)
      .filter((f) => f.isFile && f.toString.toLowerCase.endsWith(".pp"))
      .map(_.toPath)
      .toList
  }

  // TODO : Can be converted to Iterator[String]
  private def loadManifest(path: Path): List[String] = scala.io.Source.fromFile(path.toString).getLines.toList

  private def validateDir(p: Path): Boolean = Files.exists(p) && Files.isDirectory(p)
  private def modulePathValid(path: String): Boolean = 
    !(path split ':').map((p) => validateDir(Paths.get(p))).exists(_ == false)

  def prepareContent(mainFile: String, modulePath: Option[String] = None): String = {
    if(Files.isRegularFile(Paths.get(mainFile))) {

      if (modulePath.isDefined && !modulePathValid(modulePath.get))
        throw new Exception(s"Invalid module path: ${modulePath.get}")

      val modulePathList = modulePath.map(_.split(':').map(Paths.get(_)).toList) getOrElse List()
      val moduleManifests = modulePathList.map(manifestsInDirectory(_)).flatten.map(loadManifest(_)).flatten
      (loadManifest(Paths.get(mainFile)) ::: moduleManifests) mkString "\n"
    }
    else
      throw new Exception(s"Invalid manifest file $mainFile")
  }

  def compile(content: String): Graph[Resource, DiEdge] = {
    val ast = PuppetParser(content)
    val desugared_ast = DesugarPuppetAST.desugarAST(ast)
    val g =
      PuppetCompile.compile(desugared_ast.asInstanceOf[BlockStmtC]) match {
        case Left(l) => throw new Exception("Not supported")
        case Right(catalog) => catalog.toGraph
      }

    if (g.isCyclic) {
      printDOTGraph(g)
      throw new Exception("Compiled graph contains a cycle")
    }

    g
  }

  /*
  def verify(g: Graph[Resource, DiEdge]): Boolean = {

    import puppet.runtime.toposortperm._
    import puppet.verification._
    import scala.concurrent._
    import scala.concurrent.duration._
    import scala.concurrent.Future
    import scala.concurrent.ExecutionContext.Implicits.global

    import scala.util.{Try, Success, Failure}

    val permutationTrees = TopoSortPermutationTree(g)
    val resFut = Verify(permutationTrees.toSeq:_*)
    */

    /*
    val lstOfFuts = permutationTrees.toList.map((t) => Verify(t))
    val lstOfFutsTry = lstOfFuts.map(f => f.map(Success(_)).recover { case e => Failure(e) })
    val futOfLst = Future.sequence(lstOfFutsTry)
    val finalVal = Promise[Boolean]()
    futOfLst onSuccess { case lstTryB => finalVal.success(lstTryB.map(_ getOrElse false).foldLeft(true)(_ && _)) }
    futOfLst onFailure { case e => finalVal.success(false) }
    val res = Await.result(finalVal.future, Duration.Inf)
    // PuppetActorSystem.system.shutdown()
    res
    */
    /*
    Await.result(resFut, Duration.Inf)
  }
  */

  /*
  def verifyLocal(g: Graph[Resource, DiEdge]) {
    println("Number of resources in graph: " + g.nodes.size)
    val permutations = GraphTopoSortPermutations(g)
    println("Number of permutations: " + permutations.size)
    for (p <- permutations) {
      processInstallOrderLocal(p)
    }
  }
  */


  def toCoreValue(v: Value): resrc.Value = v match {
    case UndefV => resrc.UndefV
    case StringV(s) => resrc.StringV(s)
    case BoolV(b) => resrc.BoolV(b)
    case RegexV(_) => resrc.UndefV
    case ASTHashV(_) => resrc.UndefV
    case ASTArrayV(arr) => resrc.ArrayV(arr.map(toCoreValue(_))) 
    case ResourceRefV(_, _, _) => resrc.UndefV
  }

  def toCoreResource(res: Resource): resrc.Resource = {
    // Rules to convert to core resource
    val attrs = res.as.filter((a) => a.value match {
      case UndefV | StringV(_) | BoolV(_) | ASTArrayV(_) => true
      case _ => false
    })
    .map((a) => (a.name, toCoreValue(a.value))).toMap

    resrc.Resource(attrs)
  }

  // TODO : make this common as this code is shared among other modules as well
  object Eth0 {

    private val ifc = "eth0"

    import java.net.NetworkInterface
    import java.net.Inet4Address
    import scala.collection.JavaConversions._

    val ip = NetworkInterface.getByName(ifc)
      .getInetAddresses
      .toList // a list containing both ipv6 and ipv4 address
      .collect({ case ip: Inet4Address => ip.getHostAddress })
      .head
  }

  object PuppetActorSystem {

    import com.typesafe.config.ConfigFactory
    import akka.actor.{ActorSystem}

    private val akkaConf = ConfigFactory.parseString("akka.remote.netty.tcp.hostname=\"" + Eth0.ip + "\"")
      .withFallback(ConfigFactory.load.getConfig("agent"))

    lazy val masterAddress = ConfigFactory.load.getString("master")

    lazy val system = ActorSystem("PuppetInstallerSystem", akkaConf)
  }

  def verify(g: Graph[Resource, DiEdge]): Boolean = {
    // Convert to serializable Graph
    val nodes = g.nodes map ((n) => toCoreResource(n.value))
    val edges = g.edges map ((e) => toCoreResource(e.source.value) ~> toCoreResource(e.target.value))
    val gprime = Graph.from(nodes, edges)

    import puppet.common._

    val master = PuppetActorSystem.system.actorSelection(PuppetActorSystem.masterAddress)
    master ! Work(gprime)
    true
  }

  def printDOTGraph(g: Graph[Resource, DiEdge]) {
    import scalax.collection.io.dot._
    import scala.language.existentials

    val root = DotRootGraph(
      directed = true,
      id = Some("Resource_Graph"),
      kvList = Seq[DotAttr]())

    def edgeTransformer(innerEdge: Graph[Resource, DiEdge]#EdgeT):
      Option[(DotGraph, DotEdgeStmt)] = {
      val edge = innerEdge.edge
      Some(root, DotEdgeStmt(edge.from.toString,
                             edge.to.toString,
                             Nil))
    }

    def iNodeTransformer(isolatedNode: Graph[Resource, DiEdge]#NodeT):
      Option[(DotGraph, DotNodeStmt)] = {
      Some(root, DotNodeStmt(isolatedNode.toString, Nil))
    }

    val dot = g.toDot(root, edgeTransformer,
      None, None, Some(iNodeTransformer))

    println(dot)
  }
}
