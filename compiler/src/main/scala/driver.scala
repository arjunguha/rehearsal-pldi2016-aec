package puppet.driver

import puppet.parser._
import puppet.core._
import puppet.core.eval._

// import puppet.runtime.core._

import puppet.runtime.toposortperm._

import scala.util.Try
import plasma.docker._

import scalax.collection.Graph
import scalax.collection.GraphEdge._
import scalax.collection.GraphEdge._
import scalax.collection.io.json._
import scalax.collection.io.json.descriptor.predefined._

import scala.concurrent._
import scala.concurrent.duration._
import scala.util.Random

import akka.actor.{Actor, ActorSystem, ActorRef}
import akka.pattern.ask
import akka.util.Timeout
import com.typesafe.config.ConfigFactory

import ExecutionContext.Implicits.global

object PuppetDriver {

  private val dockerhost = "localhost"
  private val dockerport = 2375
  private val url = s"http://$dockerhost:$dockerport"
  private val containerName = "plasma/puppet-installer"
  private val containerPort = 8140
  private val execActorPath = "/user/ExecActor"

  private def processInstallOrder(order: Seq[Resource]): Seq[Boolean] = {
    implicit val installTimeout = Timeout(600.seconds) // TODO : Need to make configurable
    /*
     * Create a container
     * Get reference to actor running on container
     * For each resource in order, get its provider and send over to container for install
     */

    val cfg: ContainerConfig = plasma.docker.container(containerName)
      .withCommand("bash", "-c", "date") // dummy command required for container to be created
      .withNetwork(true)

    val docker = new Docker(url)
    
    val container = Await.result(docker.createContainer(cfg), Duration.Inf)
    val id = container.Id
    Await.result(docker.startContainer(id), Duration.Inf)
    val inspectCfg = Await.result(docker.inspectContainer(id), Duration.Inf)
    val containerIP = inspectCfg.NetworkSettings.IPAddress
    val gateway = inspectCfg.NetworkSettings.Gateway

    // TODO: Wait for container actor system to come up. Container should coordinate handshake
    Thread sleep 10000

    val akkaConf = ConfigFactory.parseString("akka.remote.netty.tcp.hostname=\"" + gateway + "\"")
      .withFallback(ConfigFactory.load.getConfig("agent"))

    val system = ActorSystem("Client", akkaConf)
    val remoteAddress = "akka.tcp://PuppetInstallerSystem@" + containerIP + ":" + containerPort.toString + execActorPath
    val remoteRef = system.actorSelection(remoteAddress)

    val stss = for (pb <- order)
       yield Await.result(ask(remoteRef, pb.toStringAttributes).mapTo[Boolean], Timeout(600.seconds).duration)

    system.shutdown()

    /*
    val logs = Await.result(docker.logs(id, true), Duration.Inf)
    val logstr = new String(logs)
    println("----------------------- Start container logs ----------------------")
    println(logstr)
    println("----------------------- End   container logs ----------------------")
    */

    Await.result(docker.killContainer(id), Duration.Inf)
    Await.result(docker.deleteContainer(id), Duration.Inf)
    stss
  }

  /*
  private def processInstallOrderLocal(order: Seq[Resource]) {
    for (r <- order)
      Provider(r.toStringAttributes).realize
  }
  */

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
      throw new Exception("Compiled graph contains a cycle")
    }

    g
  }

  def verify(g: Graph[Resource, DiEdge]) {
    println("Number of resources in graph: " + g.nodes.size)
    val permutations = GraphTopoSortPermutations(g)/*.par*/
    println("Number of permutations: " + permutations.size)
    for (p <- permutations) {
      val stss = processInstallOrder(p)
      if (stss.exists(_ == false))
        throw new Exception("Verification failed")
    }
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

  def printGraph(g: Graph[Resource, DiEdge]) {
    val resource_desc = new NodeDescriptor[Resource] (typeId = "Resources") {
      def id (node: Any): String = node match {
        case x: Resource  => "Resource[%s]".format(x.title)
      }
    }

    val quickJson = new Descriptor[Resource](
      defaultNodeDescriptor = resource_desc,
      defaultEdgeDescriptor = Di.descriptor[Resource]()
    )

    println(g.toJson(quickJson))
  }
}
