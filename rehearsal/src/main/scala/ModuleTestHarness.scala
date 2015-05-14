package pipeline

import pipeline.toFileScriptGraph
import puppet.Modules
import puppet.syntax.{TopLevel, parse}

object ModuleTestHarness {

  val modules = Modules("benchmarks/puppetforge-modules/modules").withoutRuby

  def loadModuleClass(name: String) = {
    val likelyClassName = name.split("/").last
    val mod = modules.loadWithDependencies(name)
    val include = parse(s"include $likelyClassName")
    val pp = TopLevel(mod.items ++ include.items)
    toFileScriptGraph(pp.desugar.toGraph(puppet.Facter.emptyEnv).head._2)
  }

}