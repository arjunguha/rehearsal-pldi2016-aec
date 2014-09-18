package puppet.verification.master

import puppet.common._

// Bootable akka that receives a graph, generate permuations and send it to worker
import akka.kernel.Bootable

// TODO: Should go into Util
object InterfaceIPV4Address {

  import java.net.NetworkInterface
  import java.net.Inet4Address
  import scala.collection.JavaConversions._

  def apply(name: String): String = NetworkInterface.getByName(name)
    .getInetAddresses
    .toList // a list containing both ipv6 and ipv4 address
    .collect({ case ip: Inet4Address => ip.getHostAddress })
    .head
}


import akka.actor.{Actor, ActorSystem, Props}

import puppet.common.resource._

import scalax.collection.Graph
import scalax.collection.GraphEdge._

case class Work(work: Any)

class Master extends Actor {

  def receive: Receive = {
    case Work(work) => println("Graph Received") // g: Graph[Resource, DiEdge] 
    case WorkerCreated(w) => println("Worker created")
    case WorkerAvailable(w) => println("Worker available")
  }
}

class BootApp extends Bootable {

  import com.typesafe.config.ConfigFactory

  private val defaults = ConfigFactory.load.getConfig("agent")

  private val ip = InterfaceIPV4Address("eth0")

  private val akkaConf = ConfigFactory.parseString("akka.remote.netty.tcp.hostname=\"" + ip + "\"")
    .withFallback(defaults)

  val system = ActorSystem("Master", akkaConf)

  def startup = system.actorOf(Props[Master])

  def shutdown = system.shutdown()
}
