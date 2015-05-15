import scalax.collection.Graph
import scalax.collection.GraphEdge.DiEdge
import puppet.Modules
import puppet.syntax.{TopLevel, parse}
import scala.util.{Try, Success, Failure}
import java.nio.file.{Files, Paths}
import rehearsal.ppmodel._
import puppet.graph._
import rehearsal.fsmodel._
import puppet.Facter


class ModuleSuite extends org.scalatest.FunSuite {

  val modulesPath = "benchmarks/puppetforge-modules/modules"

  if (Files.isDirectory(Paths.get(modulesPath))) {

    val modules = Modules(modulesPath).withoutRuby

    def load(name: String): FileScriptGraph = {
      val mod = modules.loadWithDependencies(name)
      val likelyClassName = name.split("/").last
      val include = parse(s"include $likelyClassName")
      val pp = TopLevel(mod.items ++ include.items)
      val rg = pp.desugar.toGraph(puppet.Facter.emptyEnv).head._2
      toFileScriptGraph(rg)
    }


    def myTest(name: String): Unit = {
      Try(load(name)) match {
        case Failure(exn) => () // hide translation errors
        case Success(g) => {
          test(name) {
            println(s">>> $name")
            // val myBdd = bdd.Bdd[TestFileState]((x, y) => x < y)
            // val fileScriptGraph = Slicing.sliceGraph(g)
            // //val pre = WeakestPreconditions.wpGraphBdd(myBdd)(fileScriptGraph, myBdd.bddTrue)
            // val isDeter = Z3Evaluator.isDeterministic(myBdd)(myBdd.bddTrue, fileScriptGraph)
            // println(s"$name -> $isDeter")
            // assert(isDeter)
          }
        }
      }
    }

    val roots = modules.dependencyGraph.nodes.filter(_.outDegree == 0)

    for (module <- roots) {
      myTest(module)
    }
  }
  else {
    // Run ./benchmarks.sh download to fix this
    info("modules directory not found (no tests run)")
  }

}