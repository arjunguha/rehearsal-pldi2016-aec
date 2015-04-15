package puppet.verification.common

import akka.actor.ActorRef

// Specific messages between dispatcher and worker
case class ResourceSuccess(img: String)
case class ResourceFailed(msg: String, out: String, err: String)
case class GoGoGo(img: String, res: puppet.common.resource.Resource)

// TODO: temporary
case object InstallFailed
case object InstallSuccess
