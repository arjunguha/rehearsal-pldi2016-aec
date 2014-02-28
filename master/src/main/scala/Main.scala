import akka.kernel.Bootable
import akka.pattern.ask
import akka.util.Timeout
import akka.actor.{Address, ActorSystem, Actor, Props, ActorRef}
import com.typesafe.config.ConfigFactory



class MasterActor () extends Actor {

  override def receive = {

    case _ => println ("pinged"); sender ! "Pong"
  }
}



/* Why bootable */
/* TODO : Consume Config */
class MasterSystem (config: String) extends Bootable {

  val system = ActorSystem ("Master", ConfigFactory.load.getConfig ("master"))

  override def startup  = { println("the master is online") }
  override def shutdown = { system.shutdown() }

  system.actorOf (Props (new MasterActor ()), "Register")
}
  


object Main {

  def main (args: Array[String]) {

    new MasterSystem ("config" /* TODO */)
  }
}
