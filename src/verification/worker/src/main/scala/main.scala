package puppet.verification.worker.main

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

// 'the' docker system for interacting with docker service
object Docker {

  import plasma.docker._

  private val dockerhost = "localhost"
  private val dockerport = 2375
  private val url = s"http://$dockerhost:$dockerport"
  lazy val system = new Docker(url)
}

class BootApp extends Bootable {

  import akka.actor.{Actor, ActorSystem, Props}

  import puppet.verification.common._
  import puppet.verification.worker.dispatcher._
  import puppet.verification.worker.containerfsm._

  import com.typesafe.config.ConfigFactory

  private val defaults = ConfigFactory.load.getConfig("agent")

  private val ip1 = InterfaceIPV4Address("eth0")
  private val ip2 = InterfaceIPV4Address("docker0")

  private val akkaConf1 = ConfigFactory.parseString("akka.remote.netty.tcp.hostname=\"" + ip1 + "\"")
    .withFallback(defaults)
  private val akkaConf2 = ConfigFactory.parseString("akka.remote.netty.tcp.hostname=\"" + ip2 + "\"")
    .withFallback(defaults)

  val system1 = ActorSystem("Worker", akkaConf1)
  val system2 = ActorSystem("Worker", akkaConf2)

  private val masterAddress = ConfigFactory.load.getString("master")
  private val nWorkers = ConfigFactory.load.getInt("nWorkers")

  def startup = {
    val master = system1.actorSelection(masterAddress)
    val dispatcher = system1.actorOf(Props[Dispatcher])
    
    for (_ <- 0 until nWorkers) {
      val worker = system2.actorOf(Props(new DockerContainer(Docker.system, dispatcher)))
      dispatcher ! WorkerCreated(worker)
    }

    master ! WorkerCreated(dispatcher)
  }

  def shutdown = {
    system1.shutdown()
    system2.shutdown()
  }
}
