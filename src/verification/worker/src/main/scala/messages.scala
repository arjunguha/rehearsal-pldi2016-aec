package puppet.verification.common

import akka.actor.ActorRef

case class WorkerCreated(worker: ActorRef)
case class WorkerAvailable(worker: ActorRef)
case class WorkCompleted(worker: ActorRef)
case class WorkFailed(worker: ActorRef, reason: String)

case class StartWork(work: Any)

// Specific messages between dispatcher and worker
case class ResourceSuccess(img: String)
case class ResourceFailed(msg: String, out: String, err: String)
case class GoGoGo(img: String, res: puppet.common.resource.Resource)

// TODO: temporary
case object InstallFailed
case object InstallSuccess
