package puppet.verification.worker.containerfsm

import akka.actor.{Actor, ActorRef, PoisonPill}

import plasma.docker._
import puppet.verification.common._
import puppet.verification.worker.installer._

import scala.async.Async.{async, await}
import scala.concurrent._
import scala.concurrent.Future._
import scala.concurrent.Promise._ 
import scala.concurrent.duration._
import scala.util.{Try, Success, Failure}

import ExecutionContext.Implicits.global

// Cycles through a docker container
class DockerContainer(val docker: Docker, dispatcher: ActorRef) extends Actor {

  private case object StartContainer
  private case object CreationFailed
  private case object StartFailed
  private case object InstallFailed
  private case object InstallSuccess
  private case object Commit
  private case object StopContainer
  private case object DeleteContainer

  var installer: ActorRef = context.system.deadLetters
  var containerId: Option[String] = None
  var client: ActorRef = context.system.deadLetters

  private def createInstaller(res: Resource) {
    installer = context.actorOf(Installer.props(res))
  }

  private def createContainer(image: String) = {
    val path = akka.serialization.Serialization.serializedActorPath(installer)
    
    val cfg = plasma.docker.container(image)
      .withCommand("java", "-jar", "/app/puppet-installer.jar", path)
      .withNetwork(true)

    // Returns some future
    docker.createContainer(cfg)
  }

  private def reset() {
    context.become(init)

    installer = context.system.deadLetters
    containerId = None
    client = context.system.deadLetters

    // request more work
    dispatcher ! WorkerAvailable(self)
  }

  // FSM
  def receive: Receive = init

  def init: Receive = {

    case GoGoGo(img, res) => {
      client = sender()
      createInstaller(res)
      context.become(creation)
      createContainer(img) onComplete {
        case Success(cfg) => containerId = Some(cfg.Id); self ! StartContainer
        case Failure(e) => self ! CreationFailed
      }
    }

    case _ => ()
  }

  def creation: Receive = {

    case StartContainer => {
      context.become(start)
      docker.startContainer(containerId.get) onComplete {
        case Success(_) => ()
        case Failure(e) => self ! StartFailed
      }
    }

    case CreationFailed => {
      // kill installer
      installer ! PoisonPill
      client ! ResourceFailed
      reset()
    }

    case InstallFailed => {
      if (containerId.isDefined) {
        val out = Await.result(docker.logs(containerId.get, false), Duration.Inf)
        val err = Await.result(docker.logs(containerId.get, true), Duration.Inf)
        println("*************** STDOUT ***************")
        println(new String(out))
        println("=======================================================")
        println("*************** STDERR ***************")
        println(new String(err))
        println("=======================================================")
      }
      
      installer ! PoisonPill
      client ! ResourceFailed
      reset()
    }

    case _ => ()
  }

  def start: Receive = {

    case InstallSuccess => self ! Commit

    case InstallFailed => {
      if (containerId.isDefined) {
        val out = Await.result(docker.logs(containerId.get, false), Duration.Inf)
        val err = Await.result(docker.logs(containerId.get, true), Duration.Inf)
        println("*************** STDOUT ***************")
        println(new String(out))
        println("=======================================================")
        println("*************** STDERR ***************")
        println(new String(err))
        println("=======================================================")
      }

      client ! ResourceFailed
      context.become(stop)
      self ! StopContainer
    }

    case Commit => {
      context.become(stop)
      docker.commitContainer(containerId.get) onComplete {
        case Success(img) => client ! ResourceSuccess(img); self ! StopContainer
        case Failure(r) => client ! ResourceFailed; self ! StopContainer
      }
    }

     case _ => ()
  }

  def stop: Receive = {

    // TODO: Stop vs kill
    case StopContainer => {
      context.become(delete)
      docker.killContainer(containerId.get) onComplete {
        case _ => self ! DeleteContainer
      }
    }

    case _ => ()
  }

  def delete: Receive = {

    case DeleteContainer => {
      docker.deleteContainer(containerId.get) onComplete {
        case _ => reset ()
      }
    }

    case _ => ()
  }
}

