package rehearsal

package repl {

  import scala.tools.nsc.interpreter._
  import scala.tools.nsc.Settings
  import java.nio.file.Paths
  import UpdateSynth._

  private object Main extends App {
    def uncurry[A, B, C](f: (A, B) => C)(t: (A, B)): C = f(t._1, t._2)
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
      case List("benchmark", "prefix", n, trial) => { // approx. 50
        // Synthesize the delta between two distinct manifests of size 3 with a common prefix of size n.
        println("count,time")
        0.until(Integer.parseInt(trial)).map(_ => {
          0.to(Integer.parseInt(n)).map(x => {
            val pre = genPrefix(x)
            val start = java.lang.System.currentTimeMillis()
            uncurry(execLists)(gen(3) match {
              case (a, b) =>  (pre ++ a, pre ++ b)
            })
            val end = java.lang.System.currentTimeMillis()
            println(s"$x,${end - start}")
          })
        })
      }
      case List("benchmark", "second", n, trial) => { // approx. 10
        // Grow a manifest of size n and synthesize a delta from an empty manifest.
        println("count,time")
        0.until(Integer.parseInt(trial)).map(_ => {
          0.to(Integer.parseInt(n)).map(x => {
            val start = java.lang.System.currentTimeMillis()
            uncurry(execLists)(gen(0, x * 5))
            val end = java.lang.System.currentTimeMillis()
            println(s"${x*5},${end - start}")
          })
        })
      }
      case List("benchmark", "first", n, trial) => { // approx. 5
        // Grow a manifest of size n and synthesize a delta to an empty manifest.
        println("count,time")
        0.until(Integer.parseInt(trial)).map(_ => {
          0.to(Integer.parseInt(n)).map(x => {
            val start = java.lang.System.currentTimeMillis()
            uncurry(execLists)(gen(x, 0))
            val end = java.lang.System.currentTimeMillis()
            println(s"$x,${end - start}")
          })
        })
      }
      case List("benchmark", "both", n, trial) => { // approx. 5
        // Grow two distinct manifests of the same size and find a delta.
        println("count,time")
        0.until(Integer.parseInt(trial)).map(_ => {
          0.to(Integer.parseInt(n)).map(x => {
            val start = java.lang.System.currentTimeMillis()
            uncurry(execLists)(gen(x))
            val end = java.lang.System.currentTimeMillis()
            println(s"$x,${end - start}")
          })
        })
      }
      case "is-module-deterministic" :: modules => {
        for (name <- modules) {
          val (b, t) = isDeterministic(loadModuleClass(name))
          println(s"$name,$b, $t")
        }
      }
      case "catalog-deter" :: List(catalogFile) => {
        val rg = Catalog.parseFile(catalogFile)
        println(rg)
        val g = toFileScriptGraph(rg)
        val g1 = Slicing.sliceGraph(g)
        println(rg)
        println(SymbolicEvaluator.isDeterministic(g))
      }
      case List("detersuite") => DeterminismBenchmarks.run()
      case List("detersizes") => DeterminismSizeTables.run()
      case List("deterstress") => DeterStressBenchmark.run()
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

  def isDeterministic(g: FileScriptGraph): (Boolean, Long) = {
    val g2 = Slicing.sliceGraph(g)
    time(SymbolicEvaluator.isDeterministic(g2))
  }

}
