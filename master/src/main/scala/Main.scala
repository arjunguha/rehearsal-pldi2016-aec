import akka.kernel.Bootable
import akka.actor.{Address, ActorSystem, ActorRef, Deploy, Props}
import akka.remote.RemoteScope
import com.typesafe.config.ConfigFactory
import akka.pattern.ask
import scala.collection._
import scala.concurrent._
import scala.concurrent.duration._
import akka.util.Timeout


/* Why bootable */
class MasterSystem (config: ResourceDesc, 
                    getActorProps: ((String, InstallMethod,
                                     Map[String, String],
                                     Map[String, ActorRef]) => Props)) extends Bootable {

  val system = ActorSystem ("Master", ConfigFactory.load.getConfig ("master"))

  override def startup  = { println("the master is online") }
  override def shutdown = { println ("shutting down"); system.shutdown() }

  val agent_port = 5001

  implicit val timeout = Timeout (3600 seconds)

  // TODO : Cycle Detection
  def install_resource (res: ResourceDesc,
                        cur_loc: Remote): (String , ActorRef) = {

    var install_ip = res.loc match {
      case Localhost   => cur_loc.ip
      case Remote (ip) => ip
    }

    val dep_map = res.deps.map (install_resource (_, Remote (install_ip))) toMap
    
    // TODO : Flat vs heirarchical?
    val remote_addr = Address ("akka.tcp", "WorkerSys", install_ip, agent_port)

    val ref = system.actorOf ((getActorProps (res.name,
                                      res.installation,
                                      res.props,
                                      dep_map)).withDeploy (Deploy (scope = RemoteScope (remote_addr)))/*,
                               name = res.name*/)
    val future = ref ? "ping"
    Await.result (future, timeout.duration)
    println ("Installed " + ref.path)
    (res.name, ref)
  }

  install_resource (config, Remote ("192.168.10.21"))
}
 

object Main {

  def main (args: Array[String]) { 
    
    new MasterSystem (Apply2Install.plan, Apply2ActorProps.apply)
  }
}
