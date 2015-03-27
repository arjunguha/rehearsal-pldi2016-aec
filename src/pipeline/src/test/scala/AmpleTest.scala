import pipeline._

// TODO(kgeffen) prune
import puppet.syntax._
import puppet.graph._

import eval._
import eval.Implicits._

import java.nio.file._

import org.scalatest.FunSuite

class AmpleTest extends FunSuite {

  test("Seq(p,q) evaluates fully even if p essentially skip") {
    val a: java.nio.file.Path = "/a"
    val e = Seq(Seq(Skip, Skip), Mkdir(a))
    val g = Ample.makeGraph(Ample.initState, e)
    val finalStates = getFinalStates(g)

    assert(finalStates.size == 1)
    assert(finalStates.forall(s => s.keys.exists(_ == a)))
  }

  def getFinalStates(g: Ample.MyGraph): scala.collection.mutable.Set[Ample.State] = {
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
      val resourceGraph = BenchmarkLoader.benchmarks(name).toGraph(Facter.emptyEnv)
      println("Generating expression")
      val expr = pipeline.resourceGraphToExpr(resourceGraph)
      println(s"Expression size is ${expr.size}")
      println("Generating graph")
      val evalGraph = Ample.makeGraph(Ample.initState, expr)
      val finalStates = getFinalStates(evalGraph)
      info(s"Graph has ${evalGraph.nodes.size} nodes and ${finalStates.size} final states")
    }
  }

  runBenchmark("puppet-mosh")
  runBenchmark("vagrantpress")

  def runTest(filename: String, program: String) {
    val graph = parse(program).desugar()
                              .toGraph(Map[String, String]())

    val extExpr = pipeline.resourceGraphToExpr(graph)
    // info(extExpr.pretty())
    val evalGraph = Ample.makeGraph(Ample.initState, extExpr)
    info(s"Graph has ${evalGraph.nodes.size} nodes")
    val finalStates = getFinalStates(evalGraph)
    // for (p <- finalStates) {
    //   info(p.toString)
    // }
    //l finalStates = Ample.finalStates(Ample.initState, extExpr)
    info(finalStates.size.toString)
    // for(st <- finalStates) {
    //   info(st.toString)
    // }
    //fo(finalStates.toString)
    // Files.write(Paths.get(filename), Ample.drawGraph(extExpr).getBytes)
  }
}
