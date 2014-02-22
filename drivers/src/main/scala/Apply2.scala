/* TODO : Add update and uninstall support */
/* TODO : Batching of install, doing an independent apt-get install every time is painfull */

trait Command {

  val cmd_name: String
  def exec (args: String): Int = (Cmd.exec (cmd_name + " " + args)._1)
}


trait Service {

  val svc_name: String

  // TODO : see more info about starting stopping daemons
  def start (args: String): Int = 0
  def stop  () = 0
  def restart (/* args: String */) = Cmd.exec ("/etc/init.d/" + svc_name + " " + "restart")
  var is_running = false
}


sealed trait Package {
  val pkg_name: String
  val pkg_desc: String = ""

  def preinstall (): Int = 0
  def install (): Int // Mandatory
  def postinstall (): Int = 0
}



trait LocalPackage extends Package {

  override def install (/* TODO : Configuration */): Int = 
    (Cmd.exec ("apt-get install -q -y" + " " + pkg_name))._1
}


trait NonLocalPackage extends Package {

  // TODO : make stage absract here and let NonLocalPackages provide a definition
  def stage (): Int = 0
}


class CommandLocalPackage (_pkg_name: String,
                           _cmd_name: String = "",
                           _pkg_desc: String = "") extends LocalPackage
                                                   with Command {
  override val pkg_name = _pkg_name
  override val cmd_name = if (_cmd_name == "") _pkg_name else _cmd_name
  override val pkg_desc = _pkg_desc
}




/* TODO : Need to make these singleton objects */

class DebconfUtils extends LocalPackage {
  override val pkg_name = "debconf-utils"
}


class CouchDB (val host: String = "localhost",
               val port: String = "5894") extends LocalPackage
                                          with Service {
  override val pkg_name = "couchdb"
  override val svc_name = pkg_name

  override def postinstall () = {

    Cmd.exec ("cat << 'EOF' > /etc/couchdb/local.ini\n" +
              "[httpd]\n" + 
              "bind_address = " + host + "\n" +
              "port = " + port + "\n" +
              "EOF\n")

    restart ()

    is_running = true
    0
  }
}



class Node (wget: Command,
            tar:  Command,
            make: Command,
            cppc: Command) extends NonLocalPackage
                           with Command {
  override val pkg_name = "node"
  override val cmd_name = pkg_name

  val version = "v0.10.25"

  val src = "http://nodejs.org/dist/" + version + "/" + 
            pkg_name + "-" + version + ".tar.gz"

  override def install (): Int = {
    wget.exec (src)
    tar.exec ("-xzf" + " " + pkg_name + "-" + version + ".tar.gz")
    cd (pkg_name + "-" + version)
      Cmd.exec ("./configure")
      make.exec ("")
      make.exec ("install")
    cd ("../")
  }
}

/* TODO : Notice that this is a different kind of dependency
          Notice the empty install method
 */
class Npm (node: Node) extends NonLocalPackage
                       with Command {

  override val pkg_name = "npm"
  override val cmd_name = pkg_name

  override def install () = 0
}


/* TODO : should it depend instead on node or both "npm and node"
 *        Does node always imply npm
 */
class TypeScript (npm: Npm) extends NonLocalPackage
                            with Command {
  override val pkg_name = "typescript"
  override val cmd_name = "tsc"

  override def install (): Int = 
    npm.exec ("install -g typescript@0.9.0-1")
}




class GoLang (debconfutils: Package) extends LocalPackage
                                          with Command {
  override val pkg_name = "golang"
  override val cmd_name = "go"

  override def preinstall (): Int = {
    (Cmd.exec ("cat golang.seed | debconf-set-selections"))._1
  }
}




class Apply2 (make    : Command,
              golang  : Package,
              couchdb : CouchDB, /* XXX : External dependency */
              hg      : Command,
              nginx   : Package,
              git     : Command,
              ts      : TypeScript) extends NonLocalPackage
                                    with Command
                                    with Service {


  override val pkg_name = "Apply2"
  override val cmd_name = "apply2"
  override val svc_name = cmd_name
  override val pkg_desc = "Admission system for UMass"

  val repo_loc = "https://github.com/nimishgupta/Apply2.git"

  // Should come from configuration
  var location = "./"

  override def install (/* Configuration required */): Int = {
    
    // TODO : return error codes and log stdin and stdout
    git.exec ("clone" + " " + repo_loc)

    // XXX : Could be abstracted out as this is a frequently used action
    cd ("Apply2")
      location = Cmd.pwd.toString ()
      if (0 == make.exec (""))
        ENV_PATH.append (location)
    cd ("../")
  }

  override def postinstall (/* arguments */) = {


    this.exec ("newdept sample")
    this.exec ("newreviewer" + " " +
               "scooby redbull64 \"Scooby Doo\"")

    // TODO : Need to push it into a service
    this.exec (
               "-dbhost" + " " + couchdb.host + " " +
               "-dbport" + " " + couchdb.port + " " +
               "testserver")
  }
}

object Apply2 {

  def install (what: Package) {
    what.preinstall ()
    what.install ()
    what.postinstall ()
  }

  def install () {

    /* TODO : Should have been RAII */
    val make = new CommandLocalPackage ("make")
    install (make)

    val couchdb = new CouchDB
    install (couchdb)

    val hg = new CommandLocalPackage ("mercurial", "hg")
    install (hg)

    val wget = new CommandLocalPackage ("wget")
    install (wget)

    val tar = new CommandLocalPackage ("tar")
    install (tar)

    val gcppc = new CommandLocalPackage ("g++")
    install (gcppc)

    val node = new Node (wget, tar, make, gcppc)
    install (node)

    val npm = new Npm (node)
    install (npm)

    val tsc = new TypeScript (npm)
    install (tsc)

    val nginx = new CommandLocalPackage ("nginx")
    install (nginx)

    val debconfutils = new DebconfUtils
    install (debconfutils)

    val go = new GoLang (debconfutils)
    install (go)

    val git = new CommandLocalPackage ("git")
    install (git)

    val apply2 = new Apply2 (make, go, couchdb, hg, nginx, git, tsc)
    install (apply2)
  }
}
