import akka.kernel.Bootable
import akka.util.Timeout
import akka.actor.{ActorSystem, Actor, Props, ActorRef}
import com.typesafe.config.ConfigFactory

import scala.collection.mutable.Map
import scala.concurrent.duration._

/*
// Messages exchanged
case class StartWorker(addr: String)
case class PropertyRequested (component: String, prop_key: String)
case class PropertyReply (prop: Option[Props[String]])
case class InstallResource (r: Resource)
*/


/*
object ResourceDb {

  private var m: Map[String, Resource] = Map.empty

  def add (comp: String, r: Resource) = {m += (comp -> r)}

  def query (comp: String, prop: String) : Option[Prop[String]] = {
    (m get comp) match {
      case Some (c) => (c.get_prop (prop))
      case None => None
    }
  }
}
*/



class WorkerActor(/*masterRef : ActorRef*/) extends Actor {

  /* masterRef ! StartWorker("from the worker") */

  override def receive = {

    /*
    case StartWorker(actorPath) => {
      println("got from the master")
      sender ! StartWorker("hello from master")
    }

    case InstallResource (r) => {
      println ("Installing resource " + r.name)
      r.install ()
      ResourceDb.add (r.name, r)
    }

    case PropertyRequested (component, prop_key) => {
      println ("Seeking property " + prop_key + " in " + component)
      sender ! new PropertyReply (ResourceDb.query (component, prop_key))
    } 

    case _ => {
      println("received an unknown message type")
    }*/
    case _ =>
  }
}



class WorkerActorSystem (remoteip: String = "127.0.0.1",
                         port: Int = 5000) extends Bootable {

  val system = ActorSystem("WorkerSys", ConfigFactory.load.getConfig("slave"))
  // val masterRef = system.actorFor("akka.tcp://Master@" + remoteip + ":" + port + "/user/Register")
  // why can't we get the port from the config?

  system.actorOf(Props(new WorkerActor(/*masterRef*/)), "Register")


  def startup  = println("a worker system came online")
  def shutdown = system.shutdown()
}


class MasterActor (workerRef: ActorRef) extends Actor {

  /*
  private val timeout = Timeout (120 seconds)

  val make = new Resource ("make", Native, Map.empty, Map.empty)

  workerRef ! InstallResource (make)
  val future = workerRef ? PropertyRequested (apply2.name, "isRunning")
  val result = Await.result (future, timeout.duration).asInstanceOf[Option[Prop[String]]]
  */

  override def receive = {

    /*
    case StartWorker(actorPath) => {
      println("remote worker actor from " + actorPath + " is requesting to do work")
      sender ! StartWorker("hello from master")
    }
    */

    case _ => {
      println("received an unknown message type")
    }
  }
}



class MasterSystem (workerip: String = "127.0.0.1",
                    port: Int = 5000) extends Bootable {

  val system = ActorSystem("Master", ConfigFactory.load.getConfig ("master"))
  val workerRef = system.actorFor ("akka.tcp://Worker@" + workerip + ":" + port + "/user/Register")

  override def startup  = { println("the master is online") }
  override def shutdown = { system.shutdown() }

  system.actorOf(Props (new MasterActor(workerRef)), "Register")
}


object WorkerApp {
  def main(args: Array[String]) {
    args match {
      case Array("master") => new MasterSystem()
      case _ => new WorkerActorSystem ()
    }
  }
}
