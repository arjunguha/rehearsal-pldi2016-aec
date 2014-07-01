package puppet.installer

import akka.kernel.Bootable
import akka.actor.{Props, Actor, ActorSystem}
import akka.util.Timeout
import com.typesafe.config.ConfigFactory
import scala.concurrent.duration._
import scala.sys.process._

class Exec extends Actor {
  def receive = {
    case cmd: ProcessBuilder => sender ! cmd.!
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
