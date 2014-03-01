import akka.kernel.Bootable
import akka.pattern.ask
import akka.util.Timeout
import akka.actor.{Address, ActorSystem, Actor, Props, ActorRef}
import com.typesafe.config.ConfigFactory


/* Why bootable */
class MasterSystem (config: ResourceDesc) extends Bootable {

  val system = ActorSystem ("Master", ConfigFactory.load.getConfig ("master"))

  override def startup  = { println("the master is online") }
  override def shutdown = { println ("shutting down"); system.shutdown() }

  val agent_port = "5001"



  /*
  def install_resource (r: ResourceDesc,
                        loc: ResourceLocation = Localhost): ActorRef) {

    val deps = foreach (dep <- r.deps) yield install_resource (dep, dep.loc)
    
    val remote_addr = Address ("akka.tcp", "WorkerSys", loc.ip, port)

    system.actorof( Props(classMap.classType (r.name), r.name, r.installation,)).withDeploy (Deploy (scope = RemoteScope (address))))
  }

  install_resource (config)
*/






}
  


object Main {

  def main (args: Array[String]) {

    new MasterSystem (Apply2Install.plan)
  }
}
