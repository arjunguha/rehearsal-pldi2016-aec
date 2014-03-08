/* specify a dependency graph for Apply2 */
/* Need to associate ip address */
import scala.collection._

sealed trait ResourceLocation
case object Localhost extends ResourceLocation
case class Remote (val ip: String) extends ResourceLocation


case class ResourceDesc (val name: String,
                         val installation: InstallMethod,
                         val loc: ResourceLocation = Localhost,
                         val props: Map[String, String] = Map (),
                         val deps: List[ResourceDesc] = Nil) {}

object Apply2Install {

  private val debconfutils = ResourceDesc (DebConfUtils.name, Native ("debconf-utils"))

  private val make = ResourceDesc (Make.name, Native ("make"))

  private val mercurial = ResourceDesc (Mercurial.name, Native ("mercurial"))

  private val golang = ResourceDesc ("go", Custom ("./go_setup.sh"), Localhost,
                                     Map.empty, List (debconfutils, mercurial))

  private val git  = ResourceDesc (Git.name, Native ("git"))

  private val node = ResourceDesc (Node.name, Custom ("./node_setup.sh"))

  private val ts = ResourceDesc (TypeScript.name, 
                                 Custom ("npm install -g typescript@0.9.0-1"),
                                 Localhost, Map.empty, List (node))

  private val nginx = ResourceDesc (Nginx.name, Native ("nginx"))

  private val couchdb = ResourceDesc (CouchDB.name, 
                                      Custom ("./couchdb_setup.sh"),
                                      Remote ("192.168.10.21"),
                                      Map (("host" -> "192.168.10.21"), ("port" -> "5984")))


  val plan = ResourceDesc (Apply2.name, 
                           Custom ("./apply2_setup.sh"),
                           Remote ("192.168.10.21"),
                           Map (),
                           List (make, golang, couchdb, nginx, git, ts))
}
