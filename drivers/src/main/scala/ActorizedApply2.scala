import akka.pattern.ask
import akka.util.Timeout
import akka.actor.Actor
import akka.actor.ActorRef

import scala.concurrent._
import scala.concurrent.duration._



/////////////////////////////////////////////////////////////////////////
sealed trait InstallMethod
case object Native extends InstallMethod
case class Custom (val script: String) extends InstallMethod


object InstallResource {

  type Prop = (String, String)

  def apply (name: String,
             method: InstallMethod,
             props: Prop*): Int = {
    method match {
      case Native => Cmd.exec ("apt-get install -q -y" + " " + name)._1
      case Custom (script) => Cmd.exec (script + " " + 
                                        props.foldLeft (" ") (_ + _)
                                       )._1
    }
  }
}



class Make (name: String, i: InstallMethod) extends Actor {

  override def preStart() = InstallResource (name, i)
  override def receive = {case _ =>}
}


class DebConfUtils (name: String, i: InstallMethod) extends Actor {

  override def preStart() = InstallResource (name, i)
  override def receive = {case _ =>}
}

/* TODO : See best practices */
case object GetCouchDBHost
case object GetCouchDBPort
case class CouchDBHost (val host: String) {}
case class CouchDBPort (val port: String) {}


class CouchDB (name: String,
               i: InstallMethod,
               host: String,
               port: String) extends Actor {

  override def preStart = InstallResource (name, i)
  override def receive = {

    case GetCouchDBHost => sender ! CouchDBHost (host)
    case GetCouchDBPort => sender ! CouchDBPort (port)
  }
}

class Git (name: String, i: InstallMethod) extends Actor {

  override def preStart() = InstallResource (name, i)
  override def receive = {case _ =>}
}


class CPPC (name: String, i : InstallMethod) extends Actor {

  override def preStart () = InstallResource (name, i)
  override def receive = {case _ =>}
}


class Node (name : String,
            i : InstallMethod,
            make: ActorRef,
            cppc: ActorRef) extends Actor {

  override def preStart() = InstallResource (name, i)
  override def receive = {case _ =>}
}


class TypeScript (name: String, i: InstallMethod, node: ActorRef) extends Actor {

  override def preStart() = InstallResource (name, i)
  override def receive = {case _ =>}
}

class GoLang (name: String, i: InstallMethod, debconfUtils: ActorRef) extends Actor {

  override def preStart() = InstallResource (name, i)
  override def receive = {case _ =>}
}

class Nginx (name: String, i : InstallMethod) extends Actor {

  override def preStart() = InstallResource (name, i)
  override def receive = {case _ =>}
}
 


class Apply2 (name: String,
              i: InstallMethod,
              make: ActorRef,
              golang: ActorRef, 
              couchdb: ActorRef,
              nginx: ActorRef,
              git: ActorRef,
              ts: ActorRef) extends Actor {

  implicit val timeout = Timeout (5 seconds)

  override def preStart() = {

    val cdb_host_future = couchdb ? GetCouchDBHost
    val cdb_port_future = couchdb ? GetCouchDBPort

    val cdb_host = Await.result (cdb_host_future,
                                 timeout.duration).asInstanceOf[String]
    val cdb_port = Await.result (cdb_port_future,
                                 timeout.duration).asInstanceOf[String]

    InstallResource (name, i, ("-host", cdb_host), ("-port", cdb_port))
  }

  override def receive = {case _ =>}
}
