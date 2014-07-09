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

  private val url = "http://localhost:4243"
  private val containerName = "puppet-installer"
  private val containerPort = 8140
  private val execActorPath = "/user/ExecActor"


  private def processInstallOrder(order: Seq[Resource]): Seq[Int] = {
    implicit val installTimeout = Timeout(600.seconds) // TODO : Need to make configurable
    /*
     * Create a container
     * Get reference to actor running on container
     * For each resoruce in order, get its provider and send over to container for install
     */

    val cfg: ContainerConfig = plasma.docker.container(containerName)
      .withCommand("bash", "-c", "date") // dummy command required for container to be created
      .withNetwork(true)

    val docker = new Docker(url)
    
    val container = Await.result(docker.createContainer(cfg), Duration.Inf)
    val id = container.Id
    Await.result(docker.startContainer(id), Duration.Inf)
    val inspectCfg = Await.result(docker.inspectContainer(id), Duration.Inf)
    println(inspectCfg)
    val containerIP = inspectCfg.NetworkSettings.IPAddress
    val gateway = inspectCfg.NetworkSettings.Gateway

    // TODO: Container should coordinate handshake
    Thread sleep 5000

    val akkaConf = ConfigFactory.parseString("akka.remote.netty.tcp { hostname=\"" + gateway + "\"}")
      .withFallback(ConfigFactory.load.getConfig("agent"))

    val system = ActorSystem("Client", akkaConf)
    val remoteAddress = "akka.tcp://PuppetInstallerSystem@" + containerIP + ":" + containerPort.toString + execActorPath
    val remoteRef = system.actorSelection(remoteAddress)

    val stss = for (pb <- order)
       yield Await.result(ask(remoteRef, Provider(pb).realize).mapTo[Int], Timeout(600.seconds).duration)

    system.shutdown()

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
