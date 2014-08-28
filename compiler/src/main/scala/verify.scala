package puppet.verification

import puppet.runtime.toposortperm._
import puppet.core.eval.Resource

import akka.actor.{Actor, ActorSystem, ActorRef}
import akka.actor.{ReceiveTimeout, Props, PoisonPill}
import akka.pattern.{ask, pipe}
import akka.util.Timeout

import scala.async.Async.{async, await}
import scala.concurrent._
import scala.concurrent.Future._
import scala.concurrent.Promise._ 
import scala.concurrent.duration._
import scala.util.{Try, Success, Failure}

import ExecutionContext.Implicits.global


import plasma.docker._


// Messages (Producer)
case object StartProducer
case class Token(actor: ActorRef)
case class ResourceSuccess(img: String)
case class ResourceFailed(msg: String, out: String, err: String)
case object DispatchWork
case object Result

// Messages(Throttler)
case object StartConsumer
case object Available
case object ShutdownConsumer

case class GoGoGo(img: String, res: Resource)
case object StartContainer
case object CreationFailed
case object StartFailed
case object InstallFailed
case object InstallSuccess
case object Commit
case object StopContainer
case object DeleteContainer


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

/*
object Verify {



*/


  /* Actor that co-ordinates remote execution of resource realization
   * and reports back the results
   */
/*
  class VerifyResult(val res: Resource) extends Actor {

    private val p = Promise[Unit]()
    private val title = res.title

    p.future onFailure { case _ => println(s"Resource failed: $title") }

    // Inactivity period
    context.setReceiveTimeout(5.minutes)


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
*/

  /*
   * The Props constructor accepts a by-name argument but since we loose the
   * reference of enclosing scope, it is advised to have a companion object
   * to create an actor with arguments.
   */
/*
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
*/

  /*
  private def cleanupContainer(containerId: String) {
    Docker.system.killContainer(containerId) andThen { case _ =>
      Docker.system.deleteContainer(containerId)
    }
  }
  */
/*
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
*/


class Producer(tree: Tree[Resource]) extends Actor {

  import scala.collection.mutable.{MutableList, Queue, Map}

  type DockerImage = String
  type Work = (Tree[Resource], DockerImage)

  // TODO : Reaping images?
  val images = MutableList[DockerImage]()

  private val image = "plasma/puppet-installer"

  /* If there is not any any work available then the tokens that are received
   * are queued so that work can be allotted when it becomes available
   */
  val tokens = Queue[ActorRef]()

  /* The set of resources that is being currently processed and their
   * corresponding resource handles(ActorRefs) that they occupy alongwith
   * its dependent resources that are to executed on image obtained after
   * successfull execution
   */
  val processing = Map[ActorRef, Tree[Resource]]()

  /* If there are no tokens available then available work is queued in work
   * queue to be dispatched when tokens become available
   *
   * This effectively gives us a breadth first traversal of our tree
   */
  val work = Queue[Work]()

  private def dispatch(worker: ActorRef, work: Work) {
    val (tree, image) = work
    processing += ((worker, tree))
    worker ! GoGoGo(image, tree.root)
  }

  private def completed(worker: ActorRef, image: DockerImage) {
    // Store for cleanup later
    images += image

    // Find tree being processed and add children to work queue
    val tree = processing.get(worker)
    if (tree.isDefined) {
      // Do not enqueue new work if we have encountered an error
      tree.get.children foreach ((c) => work.enqueue((c, image)))
      processing -= worker
    }
    else {
      throw new Exception(s"Completed method: No entry found for worker")
    }
  }

  private def failed(worker: ActorRef) {
    // drain all work
    work.clear()

    // Find element in processing and add children to work queue
    val tree = processing.get(worker)
    if (tree.isDefined) {
      processing -= worker
    }
    else {
      throw new Exception(s"Failed method: No entry found for worker")
    }
  }

  private val done = Promise[Unit]()

  private def result(client: ActorRef) = done.future pipeTo client 

  def receive: Receive = {

    case StartProducer => work.enqueue((tree, image))

    case Token(actor) => tokens.enqueue(actor)

    case ResourceSuccess(img) => completed(sender, img)

    case DispatchWork =>
      if (work.isEmpty && processing.isEmpty) {
        images foreach((img) => Await.result(Docker.system.removeImage(img), Duration.Inf))
        images.clear()
        println("We are done here")
        done.success(())
      }
      else {
        while(!tokens.isEmpty && !work.isEmpty)
          dispatch(tokens.dequeue(), work.dequeue)
      }

    case ResourceFailed(msg, out, err) => failed(sender())
    case Result => result(sender())
    case _ => println("Producer received an unknown message")
  }

  // TODO : Reap images somewhere
}

// TODO : can be made generic
class Throttler(val nTokens: Int, val producer: ActorRef) extends Actor {

  private def startWorkers() {
    val docker = Docker.system
    for (_ <- 0 until nTokens) {
      context.actorOf(Props(new DockerContainer(docker)))
    }
  }

  def receive: Receive = {
    case StartConsumer => startWorkers(); context.children foreach ((c) => producer ! Token(c))
    case Available => producer ! Token(sender())
    case ShutdownConsumer => // TODO : Do Something
    case _ => println("Throttler received an unknown message")
  }
}

// Cycles through a docker container
class DockerContainer(val docker: Docker) extends Actor {

  var installer: ActorRef = context.system.deadLetters
  var containerId: Option[String] = None
  var client: ActorRef = context.system.deadLetters

  private def createInstaller(res: Resource) {
    installer = context.actorOf(Installer.props(res), name = "installer")
  }

  private def createContainer(image: String) = {
    //val actorName = installer.path.name.toString.stripPrefix("$")
    val actorName = installer.path.address.toString
    println(s"$actorName")
    val system = PuppetActorSystem.name
    val ip = PuppetActorSystem.ip
    val port = PuppetActorSystem.port

    val cfg = plasma.docker.container(image)
      .withCommand("java", "-jar", "/app/puppet-installer.jar",
                   system, ip, port.toString, actorName)
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
    context.parent ! Available
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
      installer ! PoisonPill
      client ! ResourceFailed
      reset()
    }

    case _ => ()
  }

  def start: Receive = {

    case InstallSuccess => self ! Commit

    case InstallFailed => {
      client ! ResourceFailed
      context.become(stop)
      self ! StopContainer
    }

    case Commit => {
      context.become(stop)
      docker.commitContainer(containerId.get) onComplete {
        case Success(img) => client ! ResourceSuccess(img); self ! StopContainer
        case Failure(img) => client ! ResourceFailed; self ! StopContainer
      }
    }

     case _ => ()
  }

  def stop: Receive = {

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


class Installer(val res: Resource) extends Actor {

  // TODO: This future is debug only; remove after testing
  private val p = Promise[Unit]()
  private val title = res.title

  private case object InstallationFailed extends Throwable
  private case object PingTimeoutException extends Throwable
  private case object ResponseTimeoutException extends Throwable

  p.future onFailure {
    case InstallationFailed => println(s"Resource failed: $title, Installation Failed")
    case PingTimeoutException => println(s"Resource failed: $title, no activity from remote")
    case ResponseTimeoutException => println(s"Resource failed: $title, no response from remote")
  }

  // Inactivity period
  context.setReceiveTimeout(5.minutes)

  // TODO : Its going to common, pull out
  import akka.pattern.pipe

  private def result(client: ActorRef) = p.future pipeTo client

  // FSM
  def receive = handshake

  private def handshake: Receive = {
    case "ping" => sender ! res.toStringAttributes; context become response
    case "result" => result(sender)
    case ReceiveTimeout => {
      p.failure(PingTimeoutException)
      context become dead
      context.parent ! InstallFailed
    }
  }

  private def response: Receive = {
    case "success" => {
      p.success(())
      context become dead
      context.parent ! InstallSuccess
    }

    case "failure" => {
      p.failure(InstallationFailed)
      context become dead
      context.parent ! InstallFailed
    }

    case "result" => result(sender)
    case ReceiveTimeout => {
      p.failure(ResponseTimeoutException)
      context become dead
      context.parent ! InstallFailed
    }
  }

  private def dead: Receive = {
    case "result" => result(sender)
    // If someone doesn't reap me
    case ReceiveTimeout => () // context stop self
    case _ => println("Not going to process any message")
  }
}

/*
 * The Props constructor accepts a by-name argument but since we loose the
 * reference of enclosing scope, it is advised to have a companion object
 * to create an actor with arguments.
 */
object Installer { def props(res: Resource): Props = Props(new Installer(res)) }


object Verify {

  // XXX: Can be made configurable from command line
  private val maxWorkers = 100
  // private val maxWorkers = 1

  def apply(tree: Tree[Resource]): Future[Boolean] = {

    val producer = PuppetActorSystem.system.actorOf(Props(new Producer(tree)))
    val consumerCoord = PuppetActorSystem.system.actorOf(Props(new Throttler(maxWorkers, producer)))

    consumerCoord ! StartConsumer
    producer ! StartProducer

    // Timer interrupt for scheduling tasks
    PuppetActorSystem.system.scheduler.schedule(200.milliseconds, 200.milliseconds, producer, DispatchWork)

  
    implicit val timeout = Timeout(30.minutes)
    val fut = (producer ? Result).mapTo[Unit]

    // TODO :Wait for result
    future { true } 
  }
}

