package puppet.installer

import puppet.runtime.core._

import akka.kernel.Bootable
import akka.actor.{Props, Actor, ActorSystem}
import akka.util.Timeout
import com.typesafe.config.ConfigFactory
import scala.concurrent.duration._
import scala.sys.process._

import scala.collection.immutable.Map
import scala.util.Try


class Exec extends Actor {

  def receive = {
    case attrs: Map[String, String] => sender ! (Try(Provider(attrs).realize).map(_ => true) getOrElse false)
    case "ping" => sender ! "pong"
    case "shutdown" => context.system.shutdown()
    case _ => println("Unknown message received")
  }
}

object Main extends App {

  val _ = new PuppetInstaller

  class PuppetInstaller extends Bootable {

    private val ifc = "eth0"

    import java.net.NetworkInterface
    import java.net.Inet4Address
    import scala.collection.JavaConversions._

    val ip = NetworkInterface.getByName(ifc)
      .getInetAddresses
      .toList // a list containing both ipv6 and ipv4 address
      .collect({ case ip: Inet4Address => ip.getHostAddress })
      .head

    val config = ConfigFactory.parseString("akka.remote.netty.tcp.hostname=\"" + ip + "\"")
                 .withFallback(ConfigFactory.load.getConfig("agent"))
    implicit val system = ActorSystem("PuppetInstallerSystem", config)
    val execActor = system.actorOf(Props[Exec], "ExecActor")

    override def startup  = ()
    override def shutdown = system.shutdown()
  }
}
