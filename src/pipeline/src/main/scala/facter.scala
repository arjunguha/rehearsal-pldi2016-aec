package pipeline

// Puppet uses facter to produce an environment of system-specific variables.
// This module lets us either run Facter or load an environment from a
// file.
private[pipeline] object Facter {

  import java.nio.file._
  import scala.util.Try

  type Env = Map[String, String]
  val emptyEnv: Env = Map.empty

  private val parser = """(?sm)^(\w+) => (.*?)(?=(?:\s^\w+ =>|\z))""".r

    private def parseFacter(stdout: String): Env = {
      parser.findAllMatchIn(stdout)
        .map((m) => m.group(1) -> m.group(2))
        .toMap
    }

  def fromFile(p: String): Option[Env] = fromFile(Paths.get(p))

  def fromFile(p: Path) = {
    Try(parseFacter(new String(Files.readAllBytes(p)))).toOption
  }

  def run(): Option[Env] = {
    // TODO(arjun): This would be a lot simpler:
    //
    // http://www.scala-lang.org/api/current/index.html#scala.sys.process.package
    import scala.sys.{process => p}
    val newline = sys.props("line.separator")
    var outlog = ""
    var logger = p.ProcessLogger((s) => outlog += (s + newline))
    val status = p.Process("facter") ! logger
    if(status == 0) Try(parseFacter(outlog)).toOption
    else None
  }
}
