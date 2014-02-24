import akka.kernel.Bootable
import akka.actor.{Address, ActorSystem, Actor, Props, ActorRef}
import com.typesafe.config.ConfigFactory

case class StartWorker(addr: String)

class WorkerActor(masterRef : ActorRef) extends Actor {

  masterRef ! StartWorker("from the worker")

  override def receive = {
    case StartWorker(actorPath) => {
      println("got from the master")
      sender ! StartWorker("hello from master")
    }
    case _ => {
      println("received an unknown message type")
    }
  }

}

class WorkerActorSystem (remoteip: String = "127.0.0.1",
                         port: Int = 5000) extends Bootable {

  val system = ActorSystem("WorkerSys", ConfigFactory.load.getConfig("slave"))
  val masterRef = system.actorFor("akka.tcp://Master@" + remoteip + ":" + port + "/user/Register")
  // why can't we get the port from the config?

  system.actorOf(Props(new WorkerActor(masterRef)), "Register")


  def startup  = println("a worker system came online")
  def shutdown = system.shutdown()

}

class MasterActor extends Actor {

  override def receive = {

    case StartWorker(actorPath) => {
      println("remote worker actor from " + actorPath + " is requesting to do work")
      sender ! StartWorker("hello from master")
    }

    case _ => {
      println("received an unknown message type")
    }
  }


}
class MasterSystem extends Bootable {

  val system = ActorSystem("Master", ConfigFactory.load.getConfig ("master"))
  override def startup  = { println("the master is online") }
  override def shutdown = { system.shutdown() }

  system.actorOf(Props[MasterActor], "Register")
 
}

object WorkerApp {
  def main(args: Array[String]) {
    args match {
      case Array("master") => new MasterSystem()
      case _ => new WorkerActorSystem ()
    }
  }
}
