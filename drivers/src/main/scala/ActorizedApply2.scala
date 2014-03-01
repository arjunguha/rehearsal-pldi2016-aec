import akka.pattern.ask
import akka.util.Timeout
import akka.actor.Actor
import akka.actor.ActorRef
import akka.actor.Props

import scala.concurrent._
import scala.concurrent.duration._



/////////////////////////////////////////////////////////////////////////
sealed trait InstallMethod
case class Native (val name: String)   extends InstallMethod
case class Custom (val cmd: String) extends InstallMethod


object InstallResource {

  type Prop = (String, String)

  def apply (method: InstallMethod,
             props: Prop*): Int = {
    method match {
      case Native (name) => Cmd.exec ("apt-get install -q -y" + " " + name)._1
      case Custom (cmd)  => Cmd.exec (cmd + " " + 
                                      props.foldLeft (" ") (_ + _)
                                     )._1
    }
  }
}

// -----------------------------------------------------------------

class Make (i: InstallMethod) extends Actor {

  override def preStart() = InstallResource (i)
  override def receive = {case _ =>}
}

object Make {

  val name = "make"
  def akkaProps (i: InstallMethod) = Props.create (classOf[Make], i)
}
// -----------------------------------------------------------------


// -----------------------------------------------------------------

class DebConfUtils (i: InstallMethod) extends Actor {

  override def preStart() = InstallResource (i)
  override def receive = {case _ =>}
}

object DebConfUtils {

  val name = "debconf-utils"
  def akkaProps (i: InstallMethod) = Props.create (classOf[DebConfUtils], i)
}

// -----------------------------------------------------------------

/* TODO : See best practices */
case object GetCouchDBHost
case object GetCouchDBPort
case class CouchDBHost (val host: String) {}
case class CouchDBPort (val port: String) {}


class CouchDB (i: InstallMethod,
               host: String,
               port: String) extends Actor {

  override def preStart = InstallResource (i)
  override def receive = {

    case GetCouchDBHost => sender ! CouchDBHost (host)
    case GetCouchDBPort => sender ! CouchDBPort (port)
  }
}

object CouchDB {

  val name = "couchdb"
  def akkaProps (i: InstallMethod) = Props.create (classOf[CouchDB], i/* TODO : , _, _*/)
}

class Git (i: InstallMethod) extends Actor {

  override def preStart() = InstallResource (i)
  override def receive = {case _ =>}
}

object Git {
  val name = "git"
  def akkaProps (i: InstallMethod) = Props.create (classOf[Git], i)
}


class CPPC (i : InstallMethod) extends Actor {

  override def preStart () = InstallResource (i)
  override def receive = {case _ =>}
}

object CPPC {
  val name = "g++"
  def akkaProps (i: InstallMethod) = Props.create (classOf[CPPC], i)
}


class Node (i : InstallMethod,
            make: ActorRef,
            cppc: ActorRef) extends Actor {

  override def preStart() = InstallResource (i)
  override def receive = {case _ =>}
}

object Node {
  val name = "node"
  def akkaProps (i: InstallMethod) = Props.create (classOf[Node], i)
}



class TypeScript (i: InstallMethod, node: ActorRef) extends Actor {

  override def preStart() = InstallResource (i)
  override def receive = {case _ =>}
}

object TypeScript {
  val name = "tsc"
  def akkaProps (i: InstallMethod) = Props.create (classOf[TypeScript], i)
}


class GoLang (i: InstallMethod, debconfUtils: ActorRef) extends Actor {

  override def preStart() = InstallResource (i)
  override def receive = {case _ =>}
}

object GoLang {
  val name = "go"
  def akkaProps (i: InstallMethod) = Props.create (classOf[GoLang], i)
}


class Nginx (i : InstallMethod) extends Actor {

  override def preStart() = InstallResource (i)
  override def receive = {case _ =>}
}

object Nginx {
  val name = "nginx"
  def akkaProps (i: InstallMethod) = Props.create (classOf[Nginx], i)
}

 


class Apply2 (i: InstallMethod,
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

    InstallResource (i, ("-host", cdb_host), ("-port", cdb_port))
  }

  override def receive = {case _ =>}
}

object Apply2 {
  val name = "apply2"
  def akkaProps (i: InstallMethod) = Props.create (classOf[Apply2], i)
}


object classMap {

  def classType (name: String) = 
    name match {
      case "make"          => classOf[DebConfUtils]
      case "debconf-utils" => classOf[DebConfUtils]
      case "couchdb"       => classOf[CouchDB]
      case "git"           => classOf[Git]
      case "g++"           => classOf[CPPC]
      case "node"          => classOf[Node]
      case "tsc"           => classOf[TypeScript]
      case "nginx"         => classOf[Nginx]
      case "go"            => classOf[GoLang]
      case "apply2"        => classOf[Apply2]
    }
}

