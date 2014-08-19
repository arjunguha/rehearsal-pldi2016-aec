package puppet.installer

object Services {

  private val file = "/root/.services.lst"

  import puppet.util._

  def restore() {
    import java.nio.file.{Files, Paths}

    if(Files.exists(Paths.get(file))) {
      for(line <- io.Source.fromFile(file).getLines) {
        val components = line.split(":::")
        val binary = components(0)
        val path = components(1)
        val flags = components(2)
        val mode = components(3)

        ENV_PATH.append(path)
        val cmd = List(mode, binary, flags)
        Cmd.exec(cmd mkString " ")
      }
    }
  }

  def enlist(binary: String, path: String, flags: String, mode: String) {
    import java.io.FileWriter

    val fw = new FileWriter(file, true/*append*/)
    fw.write(s"${binary}:::${path}:::${flags}:::${mode}\n")
    fw.close
  }
}






