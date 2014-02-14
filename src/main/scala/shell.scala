import java.io.File
import java.io.FileOutputStream
import scala.sys.process._
import java.nio.file._

object Cmd {

  val newline = sys.props ("line.separator")
  var pwd = Paths.get ("./")

  def exec (cmd: String): (Int, String, String) = {

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

      val status: Int = Process (file.getCanonicalPath (), pwd.toFile ()) ! logger

      // Done with file delete
      file.delete ()

      // Enabled now for logging purpose
      println (outlog)
      println (errlog)

      (status, outlog, errlog)
    } catch {
      case _: java.io.IOException => (1, "", "")
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

