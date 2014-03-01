/* specify a dependency graph for Apply2 */
/* Need to associate ip address */

sealed trait ResourceLocation
case object Localhost extends ResourceLocation
case class Remote (val ip: String) extends ResourceLocation


// XXX: Apparently cannot mix default parameters with multiple parameters '*'
class ResourceDesc (val name: String,
                    val installation: InstallMethod /* = Native */,
                    val loc: ResourceLocation /* = Localhost */,
                    val deps: ResourceDesc*) {}

object Apply2Install {

  private val make = new ResourceDesc ("make", Native, Localhost)
  private val debconfutils = new ResourceDesc ("debconf-utils", Native, Localhost)
  private val golang = new ResourceDesc ("go", new Custom ("go_setup.sh"), Localhost, debconfutils)
  private val git = new ResourceDesc ("git", Native, Localhost)
  private val cppc = new ResourceDesc ("g++", Native, Localhost)
  private val node = new ResourceDesc ("node", new Custom ("node_setup.sh"), 
                                      Localhost, cppc, make)
  private val ts = new ResourceDesc ("tsc", new Custom ("npm install -g typescript@0.9.-1"), Localhost)
  private val nginx = new ResourceDesc ("nginx", Native, Localhost)

  private val couchdb = new ResourceDesc ("couchdb", Native, Remote ("agent2"))
  

  val plan = new ResourceDesc ("apply2", new Custom ("apply2_setup.sh"), Remote ("agent1"),
                                       make, golang, couchdb, nginx, git, ts)
}

