/*
 * Adopting a push model when anyone can push commands to execute on the machine
 *
 * Execute command(s) and  
 */


import akka.actor.{ActorSystem, Props}
import akka.io.IO
import spray.can.Http

/*
object Listener extends App {

  implicit val system = ActorSystem ()

  // the handler actor replies to incoming HttpRequests
  val handler = system.actorOf (Props[CookService], name = "handler")

  IO (Http) ! Http.Bind (handler, interface = "localhost", port = 9090)
}
*/
