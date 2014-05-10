import java.io.File
import java.io.FileOutputStream
import scala.sys.process._
import java.nio.file._
import scala.util.Try


case class CmdException (status: Int, outlog: String) extends Exception (outlog)

object Cmd {

  val newline = sys.props ("line.separator")
  var pwd = Paths.get ("./")

  type Prop = (String, String)

  def exec (cmd: String, extraEnv: Prop*): Try[String] = {

    // Create a temporary file
    try {
      val file = File.createTempFile ("cookpre", ".tmp")
      file.setExecutable (true)

      // Write out our cmd
      val out = new FileOutputStream (file)
      out.getChannel ().force (true)
      out.write (cmd.getBytes)
      out.close ()

      var outlog, errlog = ""

      var logger = ProcessLogger ((s) => outlog += (s + newline),
                                  (s) => errlog += (s + newline))

      println ("executing : " + cmd)
      val status = Process (file.getCanonicalPath (), Some (pwd.toFile ()), extraEnv:_*) ! logger

      // Done with file. Delete
      file.delete ()

      // Enabled now for logging purpose
      println (outlog)
      println (errlog)

      Try (if (0 == status) outlog else throw new CmdException (status, outlog))
    } catch {
      case _: java.io.IOException => throw new CmdException (-1, "Java IO Error")
    }
  }
}


object cd {

  def apply (loc: String): Int = {

    var tmp = Cmd.pwd
    tmp = tmp.resolve (loc)
    val st = Cmd.exec ("cd" + " " + tmp.toString ())._1
    if (0 == st) Cmd.pwd = tmp
    st
  }
}

/* XXX : trait "environment variable" */
object ENV_PATH {

  var elems = System.getenv ("PATH").split (':').map (Paths.get (_))

  /* Idempotent */
  def append (path: String): Int = {

    if (! elems.contains (Paths.get (path))) {
      elems = elems :+ Paths.get (path)
      (Cmd.exec ("export PATH=$PATH:" + path))._1
    }
    else { 0 }
  }
}
