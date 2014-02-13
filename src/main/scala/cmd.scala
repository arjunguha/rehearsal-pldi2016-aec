import java.io.File
import java.io.FileOutputStream
import scala.sys.process._

object Cmd {

  val newline = sys.props ("line.separator")

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

      val status: Int = (file.getCanonicalPath ()) ! logger

      // Done with file delete
      file.delete ()

      (status, outlog, errlog)
    } catch {
      case _: java.io.IOException => (1, "", "")
    }
  }
}
