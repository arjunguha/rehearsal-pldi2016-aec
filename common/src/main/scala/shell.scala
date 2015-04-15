package puppet.common.util

import scala.sys.process._
import scala.util.Try

import java.io.{File, FileOutputStream}
import java.nio.file._

object Cmd {

  val newline = sys.props("line.separator")
  var pwd = Paths.get("./")

  type Prop = (String, String)

  def exec(cmd: String, cwd: String, extraEnv: Prop*): (Int, String, String) = {

    // Create a temporary file
    val file = File.createTempFile ("cookpre", ".tmp")
    file.setExecutable(true)

    // Write out our cmd
    val out = new FileOutputStream(file)
    out.getChannel().force(true)
    out.write(cmd.getBytes)
    out.close()

    var outlog, errlog = ""

    var logger = ProcessLogger((s) => outlog += (s + newline),
                               (s) => errlog += (s + newline))

    if (!Files.isDirectory(Paths.get(cwd)))
      throw new Exception("Invalid cwd")

    val status = Process(file.getCanonicalPath(), Some(new File(cwd)), extraEnv:_*) ! logger

    // Done with file. Delete
    Try(file.delete())

    (status, outlog, errlog)
  }

  def exec(cmd: String, extraEnv: Prop*): (Int, String, String) =
    exec(cmd, pwd.toString, extraEnv:_*)
}

object cd {

  def apply (loc: String) {

    var tmp = Cmd.pwd
    tmp = tmp.resolve (loc)
    if(Cmd.exec ("cd" + " " + tmp.toString)._1 == 0)
    {
      Cmd.pwd = tmp
    }
  }
}

/* XXX : trait "environment variable" */
object ENV_PATH {

  var elems = System.getenv ("PATH").split (':').map (Paths.get (_))

  /* Idempotent */
  def append (path: String) {

    if (! elems.contains (Paths.get (path))) {
      elems = elems :+ Paths.get (path)
      Cmd.exec ("export PATH=$PATH:" + path)
    }
  }
}
