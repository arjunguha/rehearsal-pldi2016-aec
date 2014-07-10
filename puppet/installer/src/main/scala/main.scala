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
    case attrs: Map[String, String] => sender ! (Try(Provider(attrs).realize) getOrElse -1)
    case "ping" => sender ! "pong"
    case _ => println("Unknown message received")
  }
}


object Main extends App {
  val _ = new PuppetInstaller

  class PuppetInstaller extends Bootable {

    val config = ConfigFactory.load.getConfig("agent")
    implicit val system = ActorSystem("PuppetInstallerSystem", config)
    val execActor = system.actorOf(Props[Exec], "ExecActor")

    override def startup  = ()
    override def shutdown = system.shutdown()
  }
}
