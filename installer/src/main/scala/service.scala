package puppet.installer

object Services {

  private val file = "/root/.services.lst"

  import puppet.common.util._

  def isRunning(path: String, binary: String): Boolean =
    0 == Cmd.exec(s"ps -ax | grep $binary | grep -v grep")._1

  def start(path: String, binary: String, flags: Option[String] = None): Boolean = {
    val cmd = List(s"${path}/${binary}",
                   "start",
                   flags getOrElse "")
    0 == Cmd.exec(cmd mkString " ")._1
  }

  def stop(path: String, binary: String): Boolean =
    0 == Cmd.exec(s"${path}/${binary} stop")._1

  def restore(): Boolean = {
    import java.nio.file.{Files, Paths}

    if(Files.exists(Paths.get(file))) {
      for(line <- io.Source.fromFile(file).getLines) {
        val components = line.split(":::")
        val binary = components(0)
        val path = components(1)
        val flags = components(2)
        val mode = components(3)
        println(line)

        // TODO :Be more intelligent. see exprected mode, current mode and then only take action
        val cmd = List(path + binary, flags, mode)
        val (sts, out, err) = Cmd.exec(cmd mkString " ")
        println(out)
        if(0 != sts) { 
          System.err.println(s"Service $binary failed")
          System.err.println(err)
          return false
        }
      }
      true
    }
    else { true }
  }

  def enlist(binary: String, path: String, flags: String, mode: String) {
    import java.io.FileWriter

    val fw = new FileWriter(file, true/*append*/)
    fw.write(s"${binary}:::${path}:::${flags}:::${mode}\n")
    fw.close
  }
}
