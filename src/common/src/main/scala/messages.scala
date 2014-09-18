package puppet.common

import akka.actor.ActorRef

case class WorkerCreated(worker: ActorRef)
case class WorkerAvailable(worker: ActorRef)
case class WorkCompleted(worker: ActorRef)
case class WorkFailed(worker: ActorRef, reason: String)
