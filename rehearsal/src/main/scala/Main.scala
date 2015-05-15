package rehearsal

package repl {

  import scala.tools.nsc.interpreter._
  import scala.tools.nsc.Settings

  private object Main extends App {



    args match {
      case Array() => {
        def repl = new ILoop

        val settings = new Settings
        settings.Yreplsync.value = true

        //use when launching normally outside SBT
        //settings.usejavacp.value = true

        //an alternative to 'usejavacp' setting, when launching from within SBT
        settings.embeddedDefaults[Main.type]

        repl.process(settings)
      }
      case Array("is-module-deterministic", name) => {
        val b = isDeterministic(loadModuleClass(name))
        println(s"$name,$b")
      }
    }

  }

}

package object repl {

  import rehearsal.ppmodel._
  import rehearsal.fsmodel._
  import puppet.Modules
  import puppet.syntax.{TopLevel, parse}

  val modules = Modules("benchmarks/puppetforge-modules/modules").withoutRuby

  def loadModuleClass(name: String) = {
    val likelyClassName = name.split("/").last
    val mod = modules.loadWithDependencies(name)
    val include = parse(s"include $likelyClassName")
    val pp = TopLevel(mod.items ++ include.items)
    toFileScriptGraph(pp.desugar.toGraph(puppet.Facter.emptyEnv).head._2)
  }

  def isDeterministic(g: FileScriptGraph): Boolean = {
    val myBdd = bdd.Bdd[TestFileState]((x, y) => x < y)
    val fileScriptGraph = Slicing.sliceGraph(g)
    println(fileScriptGraph)
    //val pre = WeakestPreconditions.wpGraphBdd(myBdd)(fileScriptGraph, myBdd.bddTrue)
    //println(WeakestPreconditions.bddToPred(myBdd)(pre))
    Z3Evaluator.isDeterministic(myBdd)(myBdd.bddTrue, fileScriptGraph)
  }

}