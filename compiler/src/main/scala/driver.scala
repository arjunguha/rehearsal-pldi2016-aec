package puppet.driver

import puppet.parser._
import puppet.core._
import puppet.core.eval._

// import puppet.runtime.core._

import scalax.collection.Graph
import scalax.collection.GraphEdge._

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
  private def processResourceOnParentImage(res: Map[String, String],
                                           system: ActorSystem,
                                           containerName: String): String = {

    val title = res("type")+":"+res("name")

    implicit val installTimeout = Timeout(600.seconds) // TODO : Need to make configurable

    val cfg: ContainerConfig = plasma.docker.container(containerName)
      .withCommand("bash", "-c", "date") // dummy command required for container to be created
      .withNetwork(true)

    val container = Await.result(docker.createContainer(cfg), Duration.Inf)
    val id = container.Id
    Await.result(docker.startContainer(id), Duration.Inf)
    val inspectCfg = Await.result(docker.inspectContainer(id), Duration.Inf)
    val containerIP = inspectCfg.NetworkSettings.IPAddress

    // TODO: Wait for container actor system to come up. Container should coordinate handshake
    Thread sleep 5000

    val remoteAddress = s"akka.tcp://PuppetInstallerSystem@${containerIP}:${containerPort}/${execActorPath}"
    val remoteRef = system.actorSelection(remoteAddress)

    println(s"trying resource $title")
    val result = Await.result(ask(remoteRef, res).mapTo[Boolean], Timeout(600.seconds).duration)
    println("shutting down remote")
    remoteRef ! "shutdown"
    if(false == result) {
      val out = Await.result(docker.logs(id, false), Duration.Inf)
      val err = Await.result(docker.logs(id, true), Duration.Inf)
      println("*************** STDOUT ********************")
      println(new String(out))
      println("-----------------------------------------")
      
      println("*************** STDERR ********************")
      println(new String(err))
      println("-----------------------------------------")

      Await.result(docker.killContainer(id), Duration.Inf)
      Await.result(docker.deleteContainer(container.Id), Duration.Inf)
      throw new Exception(s"Processing of resource failed $title")
    }

    val imageId = Await.result(docker.commitContainer(container.Id), Duration.Inf)
    Await.result(docker.killContainer(id), Duration.Inf)
    Await.result(docker.deleteContainer(container.Id), Duration.Inf)
    imageId
  }

  private def processPermutationTree(tree: Tree[Resource],
                                     onImage: String = "plasma/puppet-installer")
                                    (implicit system: ActorSystem) {

    val root = tree.root
    val children = tree.children

    val result = Try(processResourceOnParentImage(root.toStringAttributes, system, onImage))
    val imageId = result.get
    children.foreach((c) => processPermutationTree(c, imageId))
    // After all subtrees are processed, the image is not required anymore
    docker.removeImage(imageId)
  }
  */

  def verify(g: Graph[Resource, DiEdge]) {

    import puppet.runtime.toposortperm._
    import puppet.verification._
    import scala.concurrent._
    import scala.concurrent.duration._
    import scala.concurrent.Future
    import scala.concurrent.ExecutionContext.Implicits.global

    val permutationTrees = TopoSortPermutationTree(g)
    val lst = permutationTrees.map((t) => Verify(t))
    val finalVal = Future.reduce(lst)(_ && _)
    finalVal onSuccess { case true => println("Verification Completed")
                         case false => println("Verification failed") }
    finalVal onFailure { case e => println("Verification failed: " + e) }
    Await.result(finalVal, Duration.Inf)
  }

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
