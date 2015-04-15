package puppet.installer

import puppet.runtime.core._
import puppet.common.resource._

import akka.kernel.Bootable
import akka.actor.{Props, Actor, ActorSystem, ActorRef, ActorSelection}
import akka.pattern.pipe
import akka.util.Timeout
import com.typesafe.config.ConfigFactory

import scala.collection.immutable.Map
import scala.concurrent._
import scala.concurrent.duration._
import scala.sys.process._
import scala.util.Try
import scala.concurrent.ExecutionContext.Implicits.global

case object Start

class Exec(remote: ActorSelection) extends Actor {

  def receive = {

    case Start => println("Sending ping"); remote ! "ping"

    case resource: Resource =>
      println("Resource received for installation")
      val client = sender()
      Future { 
        Try(Provider(resource).realize()).map(_ => "success") getOrElse "failure"
      } pipeTo client
    
    case "ping" => println("Ping received"); sender ! "pong"

    case "shutdown" => println("Shutting down"); context.system.shutdown()

    case _ => println("Unknown message received")
  }
}

object Exec {
  def props(remote: ActorSelection): Props = Props(new Exec(remote))
}

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
  private val akkaConf = ConfigFactory.parseString("akka.remote.netty.tcp.hostname=\"" + Eth0.ip + "\"")
    .withFallback(ConfigFactory.load.getConfig("agent"))

  lazy val system = ActorSystem("PuppetInstallerSystem", akkaConf)
}

object Main {

  def main(args: Array[String]) {

    println("Inside main")

    if (args.length != 1) {
      System.err.println("remote address expected")
      return
    }

    val remoteAddress = args(0)
    println(s"Remote address: $remoteAddress")

    // TODO: See error code and generate message
    Services.restore()

    val remote = PuppetActorSystem.system.actorSelection(remoteAddress)
    val actor = PuppetActorSystem.system.actorOf(Exec.props(remote))
    actor ! Start
    println("Exiting main")
  }
}
