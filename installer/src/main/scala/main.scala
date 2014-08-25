package puppet.installer

import puppet.runtime.core._

import akka.kernel.Bootable
import akka.actor.{Props, Actor, ActorSystem, ActorRef}
import akka.pattern.pipe
import akka.util.Timeout
import com.typesafe.config.ConfigFactory

import scala.collection.immutable.Map
import scala.concurrent._
import scala.concurrent.duration._
import scala.sys.process._
import scala.util.Try
import scala.concurrent.ExecutionContext.Implicits.global


class Exec(remote: ActorRef) extends Actor {

  def receive = {
    case "start" => remote ! "ping"
    case attrs: Map[String, String] => {
      val client = sender()
      future { 
        Try(Provider(attrs).realize).map(_ => "success") getOrElse "failure"
      } pipeTo client
    }
    case "ping" => sender ! "pong"
    case "shutdown" => context.system.shutdown()
    case _ => println("Unknown message received")
  }
}

object Exec {

  def props(remote: ActorRef): Props = Props(new Exec(remote))
}


object Main {

  def main(args: Array[String]) {

    if (args.length != 4) {
      println("remote address expected")
      return
    }

    val remoteSystem = args(0)
    val remoteIP = args(1)
    val remotePort = args(2)
    val actorName = args(3)

    val remoteAddress = s"akka.tcp://${remoteSystem}@${remoteIP}:${remotePort}/user/${actorName}"

    Services.restore()

    val _ = new PuppetInstaller(remoteAddress)
  }

  class PuppetInstaller(remoteAddress: String) extends Bootable {

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
    val remote = Await.result(system.actorSelection(remoteAddress).resolveOne(new FiniteDuration(60, SECONDS)), Duration.Inf)
    val execActor = system.actorOf(Exec.props(remote), "ExecActor")
    execActor ! "start"

    override def startup  = ()
    override def shutdown = system.shutdown()
  }
}
