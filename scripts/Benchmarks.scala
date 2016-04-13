import java.nio.file._
import java.util.concurrent.TimeUnit

val root = "parser-tests/good"

object Implicits {

  implicit class RichProcess(process: java.lang.Process) {
    import java.io.{BufferedReader, InputStreamReader}


    def attachLogger(logger: scala.sys.process.ProcessLogger): Unit = {
      def makeReader(src: BufferedReader, dst: String => Unit): Runnable = {
        new Runnable {
          override def run(): Unit = {
            try {
              var line = src.readLine()
              while (line != null) {
                dst(line)
                line = src.readLine()
              }
            }
            finally {
              src.close()
            }
          }
        }
      }

      val stdout = new BufferedReader(
        new InputStreamReader(process.getInputStream))
      val stderr = new BufferedReader(
        new InputStreamReader(process.getErrorStream))

      new Thread(makeReader(stdout, str => logger.out(str)))
      new Thread(makeReader(stderr, str => logger.err(str)))
    }

  }

}

abstract class Benchmark {

  import Implicits._

  val output = new collection.mutable.StringBuilder()

  private val logger = scala.sys.process.ProcessLogger(
    line => {
      println(line)
      output ++= line
      output += '\n'
    },
    line => println(s"ERROR: $line"))

  type Command

  def run(commandVal: Command): Boolean = {

    val p = new ProcessBuilder("sbt", "-J-Xmx4G",
      "-Dorg.slf4j.simpleLogger.defaultLogLevel=info",
      "-Dorg.slf4j.simpleLogger.logFile=rehearsal.log",
      "--warn", "set showSuccess in ThisBuild := false",
      commandVal.toString)
      .redirectError(ProcessBuilder.Redirect.PIPE)
      .redirectOutput(ProcessBuilder.Redirect.PIPE)
      .start()

    p.attachLogger(logger)

    if (p.waitFor(2, TimeUnit.MINUTES)) {
      assert(p.exitValue == 0)
      true
    }
    else {
      p.destroyForcibly().waitFor()
      false
    }
  }

}

def doSizes(output: String): Unit = {
  val sizes = new Benchmark {

    class Command(label: String, filename: String, os: String) {
      override def toString(): String = {
        s"run benchmark-pruning-size --filename $filename --label $label --os $os"
      }
    }

    def bench(label: String, filename: String, os: String = "ubuntu-trusty") = {
      if (!run(new Command(label, filename, os))) {
        assert(false, "Calculating sizes should have terminated")
      }
    }

    output ++= "Name, Before, After\n"
    bench("irc", s"$root/nfisher-SpikyIRC.pp", os = "centos-6")
    bench("monit", s"$root/dhoppe-monit.pp")
    bench("bind", s"$root/thias-bind.pp")
    bench("hosting", s"$root/puppet-hosting_deter.pp")
    bench("dns", s"$root/antonlindstrom-powerdns.pp")
    bench("xinetd", s"$root/ghoneycutt-xinetd.pp")
    bench("jpa", s"$root/pdurbin-java-jpa-tutorial.pp", os = "centos-6")
    bench("ntp", s"$root/thias-ntp.pp")
    bench("rsyslog", s"$root/xdrum-rsyslog.pp")
    bench("nginx", s"$root/BenoitCattie-puppet-nginx.pp")
    bench("amavis", s"$root/mjhas-amavis.pp")
    bench("clamav", s"$root/mjhas-clamav.pp")
    bench("logstash", s"$root/Nelmo-logstash.pp")
  }

  Files.write(Paths.get(output), sizes.output.toString.getBytes)
}

def doDeterminism(trials: Int, output: String): Unit = {
  val determinism = new Benchmark {

    class Command(val label: String, filename: String, os: String,
                  val pruning: Boolean,
                  val commutativity: Boolean,
                  deterministic: Boolean) {
      override def toString(): String = {
        s"run benchmark-determinism --filename $filename --label $label --os $os --pruning $pruning --commutativity $commutativity --deterministic $deterministic"
      }
    }

    def mayTimeout(command: Command): Unit = {
     if (run(command) == false) {
       println(s"${command.label},${command.pruning},${command.commutativity},timeout")
     }
    }

    def bench(label: String, filename: String, deterministic: Boolean,
               os: String = "ubuntu-trusty") = {
      mayTimeout(new Command(label, filename, os, false, false, deterministic)))
      mayTimeout(new Command(label, filename, os, false, true, deterministic)))
      mayTimeout(new Command(label, filename, os, true, true, deterministic)))
    }

    output ++= "Name, Pruning, Commutativity, Time\n"
    for (i <- 0.until(trials)) {
      bench("irc", s"$root/nfisher-SpikyIRC.pp", false,  os = "centos-6")
      bench("monit", s"$root/dhoppe-monit.pp", true)
      bench("bind", s"$root/thias-bind.pp", true)
      bench("hosting", s"$root/puppet-hosting_deter.pp", true)
      bench("dns", s"$root/antonlindstrom-powerdns.pp", false)
      bench("xinetd", s"$root/ghoneycutt-xinetd.pp", false)
      bench("jpa", s"$root/pdurbin-java-jpa-tutorial.pp", true, os = "centos-6")
      bench("ntp", s"$root/thias-ntp.pp", false)
      bench("rsyslog", s"$root/xdrum-rsyslog.pp", false)
      bench("nginx", s"$root/BenoitCattie-puppet-nginx.pp", true)
      bench("amavis", s"$root/mjhas-amavis.pp", true)
      bench("clamav", s"$root/mjhas-clamav.pp", true)
      bench("logstash", s"$root/Nelmo-logstash.pp", false)
    }
  }

  Files.write(Paths.get(output), determinism.output.toString.getBytes)
}

def doIdempotence(trials: Int, output: String): Unit = {
  val idempotence = new Benchmark {

    class Command(label: String, filename: String, os: String,
                  idempotent: Boolean) {
      override def toString(): String = {
        s"run benchmark-idempotence --filename $filename --label $label --os $os --idempotent $idempotent"
      }
    }

    def bench(label: String, filename: String, idempotent: Boolean,
               os: String = "ubuntu-trusty") = {
      run(new Command(label, filename, os, idempotent))
    }

    output ++= "Name, Time\n"
    for (i <- 0.until(trials)) {
      bench("monit", s"$root/dhoppe-monit.pp", true)
      bench("bind", s"$root/thias-bind.pp", true)
      bench("hosting", s"$root/puppet-hosting_deter.pp", true)
      bench("dns", s"$root/antonlindstrom-powerdns_deter.pp", true)
      bench("irc", s"$root/spiky-reduced-deterministic.pp", true, os = "centos-6")
      bench("xinetd", s"$root/ghoneycutt-xinetd_deter.pp", true)
      bench("jpa", s"$root/pdurbin-java-jpa-tutorial.pp", true, os = "centos-6")
      bench("ntp", s"$root/thias-ntp_deter.pp", true)
      bench("rsyslog", s"$root/xdrum-rsyslog_deter.pp", true)
      bench("nginx", s"$root/BenoitCattie-puppet-nginx.pp", true)
      bench("amavis", s"$root/mjhas-amavis.pp", true)
      bench("clamav", s"$root/mjhas-clamav.pp", true)
      bench("logstash", s"$root/Nelmo-logstash_deter.pp", true)
    }
  }

  Files.write(Paths.get(output), idempotence.output.toString.getBytes)
}

def doScalability(trials: Int, output: String): Unit = {
  val benchmark = new Benchmark {

    class Command(size: Int) {
      override def toString(): String = {
        s"run scalability-benchmark --size $size"
      }
    }

    def bench(size: Int) = {
      run(new Command(size))
    }

    output ++= "Size, Time\n"
    for (i <- 0.until(trials)) {
      for (j <- 1.to(7)) {
        bench(j)
      }
    }
  }

  Files.write(Paths.get(output), benchmark.output.toString.getBytes)
}

args match {
  case Array("sizes", output) => doSizes(output)
  case Array("determinism", n, output) => doDeterminism(n.toInt, output)
  case Array("idempotence", n, output) => doIdempotence(n.toInt, output)
  case Array("scalability", n, output) => doScalability(n.toInt, output)
}

