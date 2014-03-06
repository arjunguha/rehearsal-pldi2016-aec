import akka.kernel.Bootable
import akka.actor.{ActorSystem, Actor, Props, ActorRef}
import com.typesafe.config.ConfigFactory

class WorkerActorSystem () extends Bootable {

  val system = ActorSystem ("WorkerSys", ConfigFactory.load.getConfig("slave"))

  def startup  = println("a worker system came online")
  def shutdown = system.shutdown()
}


object WorkerApp { def main(args: Array[String]) { new WorkerActorSystem () }}
