import akka.kernel.Bootable
import akka.actor.{Address, ActorSystem, ActorRef, Deploy}
import akka.remote.RemoteScope
import com.typesafe.config.ConfigFactory


/* Why bootable */
class MasterSystem (config: ResourceDesc) extends Bootable {

  val system = ActorSystem ("Master", ConfigFactory.load.getConfig ("master"))

  override def startup  = { println("the master is online") }
  override def shutdown = { println ("shutting down"); system.shutdown() }

  val agent_port = 5001

  // TODO : Cycle Detection
  def install_resource (res: ResourceDesc,
                        cur_loc: Remote): (String , ActorRef) = {

    var install_ip = res.loc match {
      case Localhost   => cur_loc.ip
      case Remote (ip) => ip
    }

    val dep_map = res.deps.map (install_resource (_, Remote (install_ip))) toMap
    
    val remote_addr = Address ("akka.tcp", "WorkerSys", install_ip, agent_port)

    val ref = system.actorOf ((Apply2ActorProps (res.name,
                                      res.installation,
                                      res.props,
                                      dep_map)).withDeploy (Deploy (scope = RemoteScope (remote_addr))))
    (res.name, ref)
  }

  install_resource (config, Remote ("127.0.0.1"))
}
 

object Main {

  def main (args: Array[String]) { new MasterSystem (Apply2Install.plan) }
}
