package puppet.verification

import akka.actor.{Actor, ActorSystem, ActorRef}

import plasma.docker._

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

  class VerifyResult(val res: Resource) extends Actor {

    private val p = Promise[Boolean]()

    // Inactivity period
    context.setReceiveTimeout(10.minutes)

    private def result(client: ActorRef) {
      // return Try[Boolean] to client
      p.future onSuccess { case _ => client ! Success(true) }
      p.future onFailure { case e => client ! Failure(e) }
    }

    // FSM
    def receive = handshake

    private def handshake: Receive = {
      case "ping" => println("ping received"); sender ! res.toStringAttributes; context become response
      case "result" => result(sender)
      case ReceiveTimeout => p.failure(TimeoutException); context become dead
    }

    private def response: Receive = {
      case "success" => p.success(true); context become dead
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
  object VerifyResult {

    def props(res: Resource): Props = Props(new VerifyResult(res))
  }

  private def cleanupContainer(containerId: String) {
    Await.result(Docker.system.killContainer(containerId), Duration.Inf)
    Await.result(Docker.system.deleteContainer(containerId), Duration.Inf)
  }

  def apply(t: Tree[Resource],
            containerName: String = puppetContainerName): Future[Boolean] = {

    val root = t.root
    val children = t.children
    val actorRef = PuppetActorSystem.system.actorOf(VerifyResult.props(root)) // This creates and starts actor

    // Does this gives us the remote address?
    val actorName = actorRef.path.name.toString
    val system = PuppetActorSystem.name
    val ip = PuppetActorSystem.ip
    val port = PuppetActorSystem.port

    println(actorName)


    // launch container
    val cfg = plasma.docker.container(containerName)
      .withCommand("bash", "-c", s"java -jar /app/puppet-installer.jar $system $ip $port $actorName")
      .withNetwork(true)

    val imageId = Promise[String]()
    val result = Promise[Boolean]()

    // TODO : rewrite onSuccess and onFailure
    val c = Docker.system.createContainer(cfg)
    c onSuccess { case container => {
      implicit val timeout = Timeout(11.minutes)
      val res = (actorRef ? result) andThen {case _ => actorRef ! PoisonPill}
      res onSuccess {
        case Success(_) => imageId completeWith ((Docker.system.commitContainer(container.Id) andThen { case _ => cleanupContainer(container.Id) }))
        case Failure(e) => imageId.failure(e); cleanupContainer(container.Id)
      }
      res onFailure {
        case e => imageId.failure(e); cleanupContainer(container.Id)
      }
    }}
    c onFailure { case e => imageId.failure(e) }

    // Image processing
    imageId.future onSuccess { case img => {
      val lst = children map((c) => Verify(c, img))
      val finalVal = Future.reduce(lst)(_ && _)
      finalVal andThen { case Success(t) => result.success(t)
                         case Failure(e) => result.failure(e) } andThen { case _ => Docker.system.removeImage(img) }
    }}
    imageId.future onFailure { case e => result.failure(e) }
    result.future
  }
}
