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


import java.io.File
import java.io.FileOutputStream
import scala.sys.process._

class CookService extends Actor {

  implicit val timeout: Timeout = 1.second // for the actor 'asks'
  import context.dispatcher // ExecutionContext for the futures and scheduler

  val newline = sys.props ("line.separator")

  def execute_command (cmd: String): String = {
    // Create a temporary file
    try {
      val file = File.createTempFile ("cookpre", ".tmp")
      file.setExecutable (true)

      // Write out our cmd
      val out = new FileOutputStream (file)
      out.getChannel ().force (true)
      out.write (cmd.getBytes)
      out.close ()

      var outlog, errlog = ""

      var logger = ProcessLogger ((s) => outlog += (s + newline),
                                  (s) => errlog += (s + newline))

      val status: Int = (file.getCanonicalPath ()) ! logger

      // Done with file delete
      file.delete ()

      outlog + errlog
    } catch {
      case _: java.io.IOException => ""
    }

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
