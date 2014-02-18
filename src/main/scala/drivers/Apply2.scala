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
  val package_name: String
  val package_desc: String = ""

  def preinstall (): Int = 0
  def install (): Int // Mandatory
  def postinstall (): Int = 0
}



trait LocalPackage extends Package {

  override def install (/* TODO : Configuration */): Int = 
    (Cmd.exec ("apt-get install -q -y" + " " + package_name))._1
}

trait NonLocalPackage extends Package {}



/* TODO : Need to make these singleton objects */


/* Make encompasses autoconf automake .. */
class Make extends LocalPackage
           with Command { 
  override val package_name = "make"
  override val cmd_name = package_name
}



class CouchDB (val host: String = "localhost",
               val port: String = "5894") extends LocalPackage
                                          with Service {
  override val package_name = "couchdb"
  override val svc_name = package_name

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



class Mercurial extends LocalPackage
                with Command {
  override val package_name = "mercurial"
  override val cmd_name = "hg"
}

class Wget extends LocalPackage
                   with Command {
  override val package_name = "wget"
  override val cmd_name = package_name
}

class Tar extends LocalPackage with Command {
  override val package_name = "tar"
  override val cmd_name = package_name
}

class CPP extends LocalPackage with Command {
  override val package_name = "g++"
  override val cmd_name = package_name
}

class Node (wget: Wget,
            tar: Tar,
            make: Make,
            cppc: CPP) extends NonLocalPackage
                        with Command {
  override val package_name = "node"
  override val cmd_name = package_name

  val version = "v0.10.25"

  val src = "http://nodejs.org/dist/" + version + "/" + 
            package_name + "-" + version + ".tar.gz"

  override def install (): Int = {
    wget.exec (src)
    tar.exec ("-xzf" + " " + package_name + "-" + version + ".tar.gz")
    cd (package_name + "-" + version)
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

  override val package_name = "npm"
  override val cmd_name = package_name

  override def install () = 0
}


/* TODO : should it depend instead on node or both "npm and node"
 *        Does node always imply npm
 */
class TypeScript (npm: Npm) extends NonLocalPackage
                            with Command {
  override val package_name = "typescript"
  override val cmd_name = "tsc"

  override def install (): Int = 
    npm.exec ("install -g typescript@0.9.0-1")
}


class Nginx extends LocalPackage
            with Command {
  override val package_name = "nginx"
  override val cmd_name = package_name
}


class DebconfUtils extends LocalPackage {
  override val package_name = "debconf-utils"
}


class GoLang (debconfutils: DebconfUtils) extends LocalPackage
                                          with Command {
  override val package_name = "golang"
  override val cmd_name = "go"

  override def preinstall (): Int = {
    (Cmd.exec ("cat golang.seed | debconf-set-selections"))._1
  }
}


class Git extends LocalPackage 
          with    Command {

  override val package_name = "git"
  override val cmd_name = package_name
}


class Apply2 (make    : Make,
              golang  : GoLang,
              couchdb : CouchDB, /* XXX : External dependency */
              hg      : Mercurial,
              nginx   : Nginx,
              git     : Git,
              ts      : TypeScript) extends NonLocalPackage
                                    with Command
                                    with Service {


  override val package_name = "Apply2"
  override val cmd_name = "apply2"
  override val svc_name = cmd_name
  override val package_desc = "Admission system for UMass"


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

object Main {

  def install (what: Package) {
    what.preinstall ()
    what.install ()
    what.postinstall ()
  }

  def main (args: Array[String]) {

    /* TODO : Should have been RAII */
    val make = new Make
    install (make)

    val couchdb = new CouchDB
    install (couchdb)

    val hg = new Mercurial
    install (hg)

    val wget = new Wget
    install (wget)

    val tar = new Tar
    install (tar)

    val gcppc = new CPP
    install (gcppc)

    val node = new Node (wget, tar, make, gcppc)
    install (node)

    val npm = new Npm (node)
    install (npm)

    val tsc = new TypeScript (npm)
    install (tsc)

    val nginx = new Nginx
    install (nginx)

    val debconfutils = new DebconfUtils
    install (debconfutils)

    val go = new GoLang (debconfutils)
    install (go)

    val git = new Git
    install (git)

    val apply2 = new Apply2 (make, go, couchdb, hg, nginx, git, tsc)
    install (apply2)
  }
}
