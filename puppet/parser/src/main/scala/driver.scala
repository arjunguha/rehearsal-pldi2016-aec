package puppet.driver

import puppet.parser._
import puppet.core._
import puppet.core.eval._

import puppet.runtime.core._
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

  // TODO : Create new exception

  // TODO : Should come from configuration file
  private val url = "http://localhost:4243"
  private val containerName = "puppet-installer"
  private val containerPort = 8140

  private def processInstallOrder(order: Seq[Resource]): Seq[Int] = {
    implicit val installTimeout = Timeout(600.seconds) // TODO : Need to make configurable
    /*
     * Create a container
     * Get reference to actor running on container
     * For each resoruce in order, get its provider and send over to container for install
     */

    val cfg: ContainerConfig = plasma.docker.container(containerName)
      .withCommand("bash", "-c", "date") // dummy command required for container to be created
      .withPortMap(containerPort, "tcp")
      .withPortMap(5001, "tcp")

    val docker = new Docker(url)
    

    /* TODO : Not a very reliable port number
     * Since this function is executed in parallel, the port may not be unique among threads
     * The port may have been taken
     * 
     */
    val hostPort = 64000 + Random.nextInt(1000)
    val hostcfg = HostConfig.empty
      .bindPort(hostPort, containerPort, "tcp")
      .bindPort(5001, 5001, "tcp")

    val container = Await.result(docker.createContainer(cfg), Duration.Inf)
    val id = container.Id
    Await.result(docker.startContainer(id, hostcfg), Duration.Inf)

    val inspectCfg = Await.result(docker.inspectContainer(id), Duration.Inf)
    println (inspectCfg)

    // TODO : Get ActorRef
    val akkaConf = ConfigFactory.load.getConfig("agent")
    val system = ActorSystem("Client", akkaConf)
    val remoteAddress = "akka.tcp://PuppetInstallerSystem@127.0.0.1:" + hostPort.toString + "/user/ExecActor"
    val remoteRef = system.actorSelection(remoteAddress)


    val stss = for (pb <- order)
       yield Await.result(ask(remoteRef, pb).mapTo[Int], Timeout(600.seconds).duration)

    Await.result(docker.killContainer(id), Duration.Inf)
    Await.result(docker.deleteContainer(id), Duration.Inf)
    stss
  }

  def compile(content: String): Graph[Resource, DiEdge] = {
    val ast = PuppetParser (content)
    val desugared_ast = DesugarPuppetAST.desugarAST (ast)
    val g = 
      PuppetCompile.compile(desugared_ast.asInstanceOf[BlockStmtC]) match {
        case Left (l) => throw new Exception ("Not supported")
        case Right (catalog) => catalog.toGraph
      }

    if (g.isCyclic) {
      throw new Exception("Compiled graph contains a cycle")
    }

    g
  }

  def verify(g: Graph[Resource, DiEdge]) {
    GraphTopoSortPermutations(g)/*.par*/.foreach(processInstallOrder _)
  }

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

    println (g.toJson (quickJson))
  }
}
