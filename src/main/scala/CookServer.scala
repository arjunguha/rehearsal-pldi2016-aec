import scala.concurrent.duration._
import akka.pattern.ask
import akka.util.Timeout
import akka.actor._
import spray.can.Http
import spray.util._
import spray.http._
import spray.http.HttpHeaders._
import spray.http.ContentType._
import HttpMethods._
import MediaTypes._

class CookService extends Actor {

  implicit val timeout: Timeout = 1.second // for the actor 'asks'
  import context.dispatcher // ExecutionContext for the futures and scheduler

  def execute_command (cmd: String): String = {
    "Executing cmd: " + cmd
  }

  def receive = {

    // When a new connection comes in we register ourselves as the connection handler
    case _:Http.Connected => sender ! Http.Register (self)

    case HttpRequest (GET, Uri.Path ("/"), _, _, _) =>
      sender ! HttpResponse (entity = HttpEntity (`text/plain`, "Alive!"))

    case HttpRequest (POST, Uri.Path ("/"), headers, entity: HttpEntity.NonEmpty, protocol) =>
      println ("post request received")
      sender ! HttpResponse (entity = HttpEntity (`text/plain`, execute_command (entity.asString)))

    case _:HttpRequest => sender ! HttpResponse (status = 404, entity = "Unknown resource!")
  }
}
