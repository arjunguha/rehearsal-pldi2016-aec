import akka.kernel.Bootable
import akka.util.Timeout
import akka.actor.{ActorSystem, Actor, Props, ActorRef}
import com.typesafe.config.ConfigFactory

import scala.collection.mutable.Map
import scala.concurrent.duration._


class WorkerActor () extends Actor {

  override def receive = { case _ => }
}



class WorkerActorSystem (remoteip: String = "127.0.0.1",
                         port: Int = 5000) extends Bootable {

  val system = ActorSystem ("WorkerSys", ConfigFactory.load.getConfig("slave"))

  system.actorOf (Props[WorkerActor], "Register")

  def startup  = println("a worker system came online")
  def shutdown = system.shutdown()
}


object WorkerApp { def main(args: Array[String]) { new WorkerActorSystem () }}
