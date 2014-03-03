import akka.pattern.ask
import akka.util.Timeout
import akka.actor.Actor
import akka.actor.ActorRef
import akka.actor.Props

import scala.collection._
import scala.concurrent._
import scala.concurrent.duration._

// -----------------------------------------------------------------

class Make (i: InstallMethod) extends Actor {

  InstallResource (i)

  override def preStart() = {
    super.preStart ()
    println ("Make prestart")
  }

  override def receive = {case _ =>}
}

object Make {

  val name = "make"
  def akkaProps (i: InstallMethod,
                 props: Map[String, String],
                 deps: Map[String, ActorRef]) = Props.create (classOf[Make], i)
}
// -----------------------------------------------------------------


// -----------------------------------------------------------------

class DebConfUtils (i: InstallMethod) extends Actor {

  override def preStart() = InstallResource (i)
  override def receive = {case _ =>}
}

object DebConfUtils {

  val name = "debconf-utils"
  def akkaProps (i: InstallMethod,
                 props: Map[String, String],
                 deps: Map[String, ActorRef]) = Props.create (classOf[DebConfUtils], i)
}

// -----------------------------------------------------------------

/* TODO : See best practices */
case object GetCouchDBHost
case object GetCouchDBPort


class CouchDB (i: InstallMethod,
               host: String,
               port: String) extends Actor {

  override def preStart = InstallResource (i)
  override def receive = {

    case GetCouchDBHost => sender ! host
    case GetCouchDBPort => sender ! port
  }
}

object CouchDB {

  val name = "couchdb"
  def akkaProps (i: InstallMethod,
                 props: Map[String, String],
                 deps: Map[String, ActorRef]) = Props.create (classOf[CouchDB], i,  
                                               (props.get ("host") getOrElse "127.0.0.1"),
                                               (props.get ("port") getOrElse "5984"))
}

class Git (i: InstallMethod) extends Actor {

  override def preStart() = InstallResource (i)
  override def receive = {case _ =>}
}

object Git {
  val name = "git"
  def akkaProps (i: InstallMethod,
                 props: Map[String, String],
                 deps: Map[String, ActorRef]) = Props.create (classOf[Git], i)
}


class CPPC (i : InstallMethod) extends Actor {

  override def preStart () = InstallResource (i)
  override def receive = {case _ =>}
}

object CPPC {
  val name = "g++"
  def akkaProps (i: InstallMethod,
                 props: Map[String, String],
                 deps: Map[String, ActorRef]) = Props.create (classOf[CPPC], i)
}


class Node (i : InstallMethod,
            make: ActorRef,
            cppc: ActorRef) extends Actor {

  override def preStart() = InstallResource (i)
  override def receive = {case _ =>}
}

object Node {
  val name = "node"
  def akkaProps (i: InstallMethod,
                 props: Map[String, String],
                 deps: Map[String, ActorRef]) = Props.create (classOf[Node], i,
                   deps.get (Make.name) getOrElse (throw new IllegalArgumentException
                                                   ("Make actor ref not found")),
                   deps.get (CPPC.name) getOrElse (throw new IllegalArgumentException
                                                   ("Cpp compiler actor ref not found")))
}



class TypeScript (i: InstallMethod, node: ActorRef) extends Actor {

  override def preStart() = InstallResource (i)
  override def receive = {case _ =>}
}

object TypeScript {
  val name = "tsc"
  def akkaProps (i: InstallMethod,
                 props: Map[String, String],
                 deps: Map[String, ActorRef]) = Props.create (classOf[TypeScript], i,
                   deps.get (Node.name) getOrElse (throw new IllegalArgumentException 
                                                   ("Node actor ref not found")))
}


class GoLang (i: InstallMethod, debconfUtils: ActorRef) extends Actor {

  override def preStart() = InstallResource (i)
  override def receive = {case _ =>}
}

object GoLang {
  val name = "go"
  def akkaProps (i: InstallMethod,
                 props: Map[String, String],
                 deps: Map[String, ActorRef]) = Props.create (classOf[GoLang], i,
                         deps.get (DebConfUtils.name) getOrElse (throw new IllegalArgumentException ("debconf-utils actor ref not found")))
}


class Nginx (i : InstallMethod) extends Actor {

  override def preStart() = InstallResource (i)
  override def receive = {case _ =>}
}

object Nginx {
  val name = "nginx"
  def akkaProps (i: InstallMethod,
                 props: Map[String, String],
                 deps: Map[String, ActorRef]) = Props.create (classOf[Nginx], i)
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
  def akkaProps (i: InstallMethod, 
                 props: Map[String, String],
                 deps: Map[String, ActorRef]) = Props.create (classOf[Apply2], i,
              // TODO : Not maintainable, depends on position of args and easy to get wrong
                      deps.get (Make.name) getOrElse (throw new IllegalArgumentException 
                                                      ("Make actor ref not found")),
                      deps.get (GoLang.name) getOrElse (throw new IllegalArgumentException                                                         ("GoLang actor ref not found")),
                      deps.get (CouchDB.name) getOrElse (throw new IllegalArgumentException
                                                      ("CouchDB actor ref not found")),
                      deps.get (Nginx.name) getOrElse (throw new IllegalArgumentException
                                                      ("Nginx actor ref not found")),
                      deps.get (Git.name) getOrElse (throw new IllegalArgumentException
                                                      ("Git actor ref not found")),
                      deps.get (TypeScript.name) getOrElse (throw new IllegalArgumentException
                                                      ("TypeScript actor ref not found")))
}


object Apply2ActorProps {

  def apply (name: String, i: InstallMethod, 
             props: Map[String, String],
             deps : Map[String, ActorRef]) =

    name match {
      case "make"          => Make.akkaProps         (i, props, deps)
      case "debconf-utils" => DebConfUtils.akkaProps (i, props, deps)
      case "couchdb"       => CouchDB.akkaProps      (i, props, deps)
      case "git"           => Git.akkaProps          (i, props, deps)
      case "g++"           => CPPC.akkaProps         (i, props, deps)
      case "node"          => Node.akkaProps         (i, props, deps)
      case "tsc"           => TypeScript.akkaProps   (i, props, deps)
      case "nginx"         => Nginx.akkaProps        (i, props, deps)
      case "go"            => GoLang.akkaProps       (i, props, deps)
      case "apply2"        => Apply2.akkaProps       (i, props, deps)
    }
}
