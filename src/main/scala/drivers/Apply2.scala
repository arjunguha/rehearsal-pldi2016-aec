/* TODO :
 *   trait Package
 *   trait MemberPackage
 *   trait Native (* Available without explicitly installing *)
 *   trait NonMemberPackage
 *   trait Command
 *
 * TODO : Add update and uninstall support 
 */



/* XXX : trait "environment variable" */
object PATH {

  /* TODO : Constructor */
  
  /* Idempotent */
  def add (path: String): Int = 0
}


trait Command {

  val cmd_name: String

  def exec (args: String): Int = (Cmd.exec (cmd_name + " " + args)._1)
}


trait Service {

  def start (args: String) = 0
  def stop  () = 0
  def restart (args: String) = 0
  def is_running = false
}


trait LocalPackage {

  val package_name: String
  val package_desc: String = ""

  def preinstall = 0
  def install (/* TODO : Configuration */): Int = 
    (Cmd.exec ("apt-get install " + package_name))._1
  def postinstall = 0
}

trait NonLocalPackage {

  val package_name: String
  val package_desc: String = ""

  def preinstall = 0
  def install (): Int
  def postinstall = 0
}



/* TODO : Need to make these singleton */


/* Make encompasses autoconf automake .. */
class Make extends LocalPackage
           with Command { 
  override val package_name = "make"
  override val cmd_name = package_name
}
                                
class CouchDB extends LocalPackage
              with Command {
  override val package_name = "couchdb"
  override val cmd_name = package_name
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


/* should it depend instead on npm or both "npm and node"
 * Does node always imply npm
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


object cd {

  def apply (loc: String): Int = (Cmd.exec ("cd" + " " + loc))._1
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
  override val package_desc = "Admission system for UMass"


  val repo_loc = "https://github.com/plasma-umass/Apply2.git"

  // Should come from configuration
  val location = "./"

  override def install (/* Configuration required */): Int = {
    
    // TODO : return error codes and log stdin and stdout
    git.exec ("clone" + " " + repo_loc)

    // XXX : Could be abstracted out as this is a frequently used action
    Cmd.exec ("cd Apply2")

    make.exec ("")
  }

  override def postinstall (/* arguments */) = PATH.add (location)
}
