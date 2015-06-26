package rehearsal

package repl {

  import scala.tools.nsc.interpreter._
  import scala.tools.nsc.Settings
  import java.nio.file.Paths

  private object Main extends App {

    args.toList match {
      case List() => {
        def repl = new ILoop

        val settings = new Settings
        settings.Yreplsync.value = true

        //use when launching normally outside SBT
        //settings.usejavacp.value = true

        //an alternative to 'usejavacp' setting, when launching from within SBT
        settings.embeddedDefaults[Main.type]

        repl.process(settings)
      }
      case List("update", manifest1, manifest2) => {
        UpdateSynth.calculate(Paths.get(manifest1), Paths.get(manifest2))
      }
      case "is-module-deterministic" :: modules => {
        for (name <- modules) {
          val (b, t) = isDeterministic(loadModuleClass(name))
          println(s"$name,$b, $t")
        }
      }
      case args => {
        sys.error(s"Invalid command-line arguments: $args")
      }
    }

  }

}

package object repl {

  import puppet.Modules
  import puppet.syntax.{TopLevel, parse}

  val modules = Modules("benchmarks/puppetforge-modules/modules").withoutRubyAndInvalidDeps

  def loadModuleClass(name: String) = {
    val likelyClassName = name.split("/").last
    val mod = modules.loadWithDependencies(name)
    val include = parse(s"include $likelyClassName")
    val pp = TopLevel(mod.items ++ include.items)
    toFileScriptGraph(pp.desugar.toGraph(puppet.Facter.emptyEnv).head._2)
  }

  def time[A](thunk: => A): (A, Long) = {
    val start = System.currentTimeMillis
    val r = thunk
    val duration = System.currentTimeMillis - start
    r -> duration
  }

  def isDeterministic(g: FileScriptGraph): (Boolean, Long) = {
    val g2 = Slicing.sliceGraph(g)
    time(SymbolicEvaluator2.isDeterministic(g2))
  }

}