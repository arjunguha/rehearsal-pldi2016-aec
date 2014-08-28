package puppet.installer

import puppet.runtime.core._

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

class Exec(remote: ActorSelection) extends Actor {

  def receive = {
    case "start" => remote ! "ping"
    case attrs: Map[String, String] =>
      val client = sender()
      future { 
        Try(Provider(attrs).realize()).map(_ => "success") getOrElse "failure"
      } pipeTo client
    
    case "ping" => sender ! "pong"
    case "shutdown" => context.system.shutdown()
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

    if (args.length != 4) {
      System.err.println("remote address expected")
      return
    }

    val remoteSystem = args(0)
    val remoteIP = args(1)
    val remotePort = args(2)
    val actorName = args(3)

    val remoteAddress = s"akka.tcp://${remoteSystem}@${remoteIP}:${remotePort}/user/$$${actorName}"
    println(s"Remote address: $remoteAddress")

    // TODO: See error code and generate message
    Services.restore()

    // val _ = new PuppetInstaller(remoteAddress)
    val remote = PuppetActorSystem.system.actorSelection(remoteAddress)
    val actor = PuppetActorSystem.system.actorOf(Exec.props(remote))
    actor ! "start"
    println("Exiting main")
  }
}
