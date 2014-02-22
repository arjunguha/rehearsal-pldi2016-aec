object Main {

  def usage () = println ("... <driver name>")

  def main (args: Array[String]): Unit = {

    if (args.length != 1) {
      usage ()
      1
    }

    args(0) match {

      case "Apply2" => Apply2.install ()
      case drv:String => println ("Invalid choice, driver not available for " + drv)
    }
  }
}

