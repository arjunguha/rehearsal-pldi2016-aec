package puppet.verification.worker.dispatcher

import akka.actor.{Actor, ActorSystem, ActorRef, Terminated}
import akka.util.Timeout
import plasma.docker._
import puppet.verification.common._

import scala.async.Async.{async, await}
import scala.concurrent._
import scala.concurrent.Future._
import scala.concurrent.Promise._ 
import scala.concurrent.duration._
import scala.util.{Try, Success, Failure}

import ExecutionContext.Implicits.global

class Dispatcher extends Actor {

  case object DispatchWork

  import scala.collection.mutable.{MutableList, Queue, Map, Set}

  type DockerImage = String
  // tODO : remove Any
  type Work = (Tree[Resource], DockerImage)

  // TODO : Reaping images?
  val images = MutableList[DockerImage]()

  private val image = "plasma/puppet-installer"

  // Timer interrupt for scheduling tasks
  context.system.scheduler.schedule(200.milliseconds, 200.milliseconds, self, DispatchWork)

  /*
   * Workers that are ready to work are stored. Work is dispatched when
   * available
   */
  val workers = Set[ActorRef]()

  /* The set of resources that is being currently processed and their
   * corresponding resource handles(ActorRefs) that they occupy alongwith
   * its dependent resources that are to executed on image obtained after
   * successfull execution
   */
  val processing = Map[ActorRef, Tree[Resource]]()

  /* Work is queued to be dispatched to worker when a worker becomes free.
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

    // We are done processing element, remove it from processing queue
    val tree = processing.get(worker)
    if (tree.isDefined) {
      processing -= worker
    }
    else {
      throw new Exception(s"Failed method: No entry found for worker")
    }
  }

  def receive: Receive = {

    // Worker created? => install deathwatch
    case WorkerCreated(worker) => {
      context.watch(worker);
      workers += worker
    }

    case WorkerAvailable(worker) => workers += worker

    case Terminated(worker) => {
      /*
       * TODO : appropriate cleanup
       *   If already working on something then queue the work again
       *   check worker queue/set
       */
    }

    case ResourceSuccess(img) => completed(sender, img)

    case DispatchWork =>

      if (work.isEmpty && processing.isEmpty) {
        // TODO: remove images
        //images foreach((img) => Try(Await.result(Docker.system.removeImage(img), Duration.Inf)))
        images.clear()
        println("We are done here")
      }
      else {
        while(!workers.isEmpty && !work.isEmpty)
          dispatch(workers.head, work.dequeue())
      }

    case ResourceFailed(msg, out, err) => failed(sender())
    case _ => println("Producer received an unknown message")
  }
}
