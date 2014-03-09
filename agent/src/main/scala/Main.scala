import akka.kernel.Bootable
import akka.actor.{ActorSystem, Actor, Props, ActorRef}
import com.typesafe.config.ConfigFactory

class WorkerActorSystem (ip: Option[String]) extends Bootable {

  val config = ip match {
    case Some (ip) => ConfigFactory.parseString ("akka.remote.netty.tcp { hostname=\"" + ip + "\"}")
                      .withFallback (ConfigFactory.load.getConfig ("agent"))
    case None => ConfigFactory.load.getConfig ("agent")
  }

  val system = ActorSystem ("WorkerSys", config)

  def startup  = println("An agent system came online")
  def shutdown = system.shutdown()
}


object WorkerApp { 
  
  def main(args: Array[String]) { 
  
    args match {
      case Array (ip) => new WorkerActorSystem (Some (ip))
      case _          => new WorkerActorSystem (None)
    }
  }
}
