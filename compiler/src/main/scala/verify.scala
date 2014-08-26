package puppet.verification

import akka.actor.{Actor, ActorSystem, ActorRef}

import plasma.docker._

// 'the' docker system for interacting with docker service
object Docker {
  private val dockerhost = "localhost"
  private val dockerport = 2375
  private val url = s"http://$dockerhost:$dockerport"
  lazy val system = new Docker(url)
}

object InterfaceIPV4Address {

  import java.net.NetworkInterface
  import java.net.Inet4Address
  import scala.collection.JavaConversions._

  def apply(name: String): String = NetworkInterface.getByName(name)
    .getInetAddresses
    .toList // a list containing both ipv6 and ipv4 address
    .collect({ case ip: Inet4Address => ip.getHostAddress })
    .head
}

// 'the' actor system
object PuppetActorSystem {
  private val nwIfc = "docker0"

  import com.typesafe.config.ConfigFactory

  val ip = InterfaceIPV4Address(nwIfc)
  private val akkaConf = ConfigFactory.parseString("akka.remote.netty.tcp.hostname=\"" + ip + "\"")
    .withFallback(ConfigFactory.load.getConfig("agent"))

  val name = "PuppetVerifier"
  val port = akkaConf.getInt("akka.remote.netty.tcp.port")

  lazy val system = ActorSystem(name, akkaConf)
}

object Verify {

  import akka.actor.{ReceiveTimeout, Props, PoisonPill}
  import akka.pattern.ask
  import akka.util.Timeout

  import scala.async.Async.{async, await}
  import scala.concurrent._
  import scala.concurrent.Future._
  import scala.concurrent.Promise._ 
  import scala.concurrent.duration._
  import scala.util.{Try, Success, Failure}

  import ExecutionContext.Implicits.global

  import puppet.runtime.toposortperm._
  import puppet.core.eval.Resource

  private case object InstallationFailed extends Throwable
  private case object TimeoutException extends Throwable

  private val puppetContainerName = "plasma/puppet-installer"

  /* Actor that co-ordinates remote execution of resource realization
   * and reports back the results
   */
  class VerifyResult(val res: Resource) extends Actor {

    private val p = Promise[Unit]()
    private val title = res.title

    p.future onFailure { case _ => println(s"Resource failed: $title") }

    // Inactivity period
    context.setReceiveTimeout(5.minutes)

    import akka.pattern.pipe

    private def result(client: ActorRef) = p.future pipeTo client

    // FSM
    def receive = handshake

    private def handshake: Receive = {
      case "ping" => sender ! res.toStringAttributes; context become response
      case "result" => result(sender)
      case ReceiveTimeout => p.failure(TimeoutException); context become dead
    }

    private def response: Receive = {
      case "success" => p.success(()); context become dead
      case "failure" => p.failure(InstallationFailed); context become dead
      case "result" => result(sender)
      case ReceiveTimeout => p.failure(TimeoutException); context become dead
    }

    private def dead: Receive = {
      case "result" => result(sender)
      // If someone doesn't reap me
      case ReceiveTimeout => context stop self
      case _ => println("Not going to process any message")
    }
  }

  /*
   * The Props constructor accepts a by-name argument but since we loose the
   * reference of enclosing scope, it is advised to have a companion object
   * to create an actor with arguments.
   */
  object VerifyResult { def props(res: Resource): Props = Props(new VerifyResult(res)) }

  private def printStdout(containerId: String, title: String) {
    val strm = Await.result(Docker.system.logs(containerId, false), Duration.Inf)
    
    println(s"******************* STDOUT for $title ******************")
    println(new String(strm))
    println("========================================================")
  }

  private def printStderr(containerId: String, title: String) = {
    val strm = Await.result(Docker.system.logs(containerId, true), Duration.Inf)

    println(s"******************* STDERR for $title ******************")
    println(new String(strm))
    println("========================================================")
  }

  /*
  private def cleanupContainer(containerId: String) {
    Docker.system.killContainer(containerId) andThen { case _ =>
      Docker.system.deleteContainer(containerId)
    }
  }
  */
  private def cleanupContainer(containerId: String) {
    Try(Await.result(Docker.system.killContainer(containerId), Duration.Inf))
    Try(Await.result(Docker.system.deleteContainer(containerId), Duration.Inf))
  }

  def apply(t: Tree[Resource],
            containerName: String = puppetContainerName): Future[Boolean] = {

    val root = t.root
    val children = t.children
    val actorRef = PuppetActorSystem.system.actorOf(VerifyResult.props(root)) // This creates and starts actor

    val actorName = actorRef.path.name.toString.stripPrefix("$")
    val system = PuppetActorSystem.name
    val ip = PuppetActorSystem.ip
    val port = PuppetActorSystem.port

    // launch container
    val cfg = plasma.docker.container(containerName)
      .withCommand("java", "-jar", "/app/puppet-installer.jar",
                   system, ip, port.toString, actorName)
      .withNetwork(true)

    val imageId = Docker.system.createContainer(cfg).flatMap { container =>

      implicit val timeout = Timeout(5.minutes)
      
      val img: Future[String] = for {
        _ <- Docker.system.startContainer(container.Id)
        _ <- (actorRef ? "result") andThen {case _ => actorRef ! PoisonPill}
        img <- Docker.system.commitContainer(container.Id) 
      } yield img

      // Make sure we cleanup after we are done
      img andThen { case Failure(_) => printStdout(container.Id, root.title)
                                       printStderr(container.Id, root.title)
                                       cleanupContainer(container.Id)
                    case _ => cleanupContainer(container.Id) }
    }

    // Image processing
    imageId flatMap { id =>
      val lstOfFuts = children map((c) => Verify(c, id))
      
      val lstOfFutsTry = lstOfFuts.map(f => f.map(v => Success(v)).recover { case e => Failure(e) })
      val futOfLst = Future.sequence(lstOfFutsTry)
      val res = futOfLst.map { lstTryB => lstTryB.map(_ getOrElse false).foldLeft(true)(_ && _) }

      // Make sure we cleanup after we are done
      res andThen { case _ => Try(Await.result(Docker.system.removeImage(id), Duration.Inf)) }
    }
  }
}
