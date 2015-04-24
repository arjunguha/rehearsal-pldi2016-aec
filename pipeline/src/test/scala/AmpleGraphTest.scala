import pipeline._

// TODO(kgeffen) prune
import puppet.syntax._
import puppet.graph._
import puppet.Facter

import eval._
import eval.Implicits._

import java.nio.file._

import org.scalatest.FunSuite

class AmpleGraphTest extends FunSuite {

/*
  test("Seq(p,q) evaluates fully even if p essentially skip") {
    val a: java.nio.file.Path = "/a"
    val e = Seq(Seq(Skip, Skip), Mkdir(a))
    val g = Ample.makeGraph(Ample.initState, e)
    val finalStates = getFinalStates(g)

    assert(finalStates.size == 1)
    assert(finalStates.forall(s => s.keys.exists(_ == a)))
  }
*/

  def getFinalStates(g: AmpleGraph.MyGraph): scala.collection.mutable.Set[AmpleGraph.State] = {
    g.nodes.filter(n => n.outDegree == 0).map(_.value.state)
  }

  test("single package without attributes") {
    val program = """package{"sl": }"""
    runTest("1.dot", program)
  }


  test("2 package dependent install") {
    val program = """package{"sl": }
                     package{"cmatrix":
                       require => Package['sl']
                     }"""
    runTest("2.dot", program)
  }

  test("2 package install") {
    val program = """package{["cmatrix",
                              "telnet"]: }"""
    runTest("3.dot", program)
  }

  test("3 package install") {
    val program = """package{["sl",
                              "cowsay",
                              "cmatrix"]: }"""
    runTest("4.dot", program)
  }


  def runBenchmark(name: String) {
    test(name) {
      println("Generating resource graph")
      val resourceGraph = BenchmarkLoader.benchmarks(name)
        .toGraph(Facter.emptyEnv).head._2
      println("Generating expression")
      // val expr = pipeline.resourceGraphToExpr(resourceGraph)
      // println(s"Expression size is ${expr.size}")
      println("Generating graph")
      val evalGraph = AmpleGraph.makeGraph(Ample.initState, resourceGraph)(pipeline.GraphResourceToExpr)
      val finalStates = getFinalStates(evalGraph)
      info(s"Graph has ${evalGraph.nodes.size} nodes and ${finalStates.size} final states")
    }
  }

  runBenchmark("puppet-mosh")
  runBenchmark("vagrantpress")

  def runTest(filename: String, program: String) {
    val graph = parse(program).desugar()
                              .toGraph(Map[String, String]())
                              .head._2

    val evalGraph = AmpleGraph.makeGraph(Ample.initState, graph)(pipeline.GraphResourceToExpr)
    info(s"Graph has ${evalGraph.nodes.size} nodes")
    val finalStates = getFinalStates(evalGraph)

    info(finalStates.size.toString)
    evalGraph.saveDotFile(filename)
    
  }
}
