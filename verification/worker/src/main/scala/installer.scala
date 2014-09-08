package puppet.verification.worker.installer

import akka.actor.{Actor, ActorRef, ReceiveTimeout, Props}

import scala.async.Async.{async, await}
import scala.concurrent._
import scala.concurrent.Future._
import scala.concurrent.Promise._ 
import scala.concurrent.duration._
import scala.util.{Try, Success, Failure}

import ExecutionContext.Implicits.global

class Installer(val res: Resource) extends Actor {

  // TODO: This future is debug only; remove after testing
  private val p = Promise[Unit]()
  private val title = res.title

  private case object InstallationFailed extends Throwable
  private case object PingTimeoutException extends Throwable
  private case object ResponseTimeoutException extends Throwable

  p.future onComplete {
    case Success(_) => println(s"Resource successfull: $title")
    case Failure(InstallationFailed) => println(s"Resource failed: $title, Installation Failed")
    case Failure(PingTimeoutException) => println(s"Resource failed: $title, no activity from remote")
    case Failure(ResponseTimeoutException) => println(s"Resource failed: $title, no response from remote")
    case Failure(_) => println(s"Resource failed: $title, Unknown Reason")
  }

  // Inactivity period
  context.setReceiveTimeout(5.minutes)

  // TODO : Its going to common, pull out
  import akka.pattern.pipe

  private def result(client: ActorRef) = p.future pipeTo client

  // FSM
  def receive = handshake

  private def handshake: Receive = {
    case "ping" => {
      sender ! res.toStringAttributes
      context become response

      // Allow 20 minutes for resource installation
      context.setReceiveTimeout(20.minutes)
    }

    case "result" => result(sender)

    case ReceiveTimeout => {
      // ping message timed out

      p.failure(PingTimeoutException)
      context become dead
      context.parent ! InstallFailed
      // Turn off timer
      context.setReceiveTimeout(Duration.Inf)
    }
  }

  private def response: Receive = {
    case "success" => {
      p.success(())
      context become dead
      context.parent ! InstallSuccess
      // Turn off timer
      context.setReceiveTimeout(Duration.Inf)
    }

    case "failure" => {
      p.failure(InstallationFailed)
      context become dead
      context.parent ! InstallFailed
      // Turn out timer
      context.setReceiveTimeout(Duration.Inf)
    }

    case "result" => result(sender)

    case ReceiveTimeout => {
      p.failure(ResponseTimeoutException)
      context become dead
      context.parent ! InstallFailed
      // Turn off timer
      context.setReceiveTimeout(Duration.Inf)
    }
  }

  private def dead: Receive = {
    case "result" => result(sender)
    case _ => println("Not going to process any message")
  }
}

/*
 * The Props constructor accepts a by-name argument but since we loose the
 * reference of enclosing scope, it is advised to have a companion object
 * to create an actor with arguments.
 */
object Installer { def props(res: Resource): Props = Props(new Installer(res)) }

