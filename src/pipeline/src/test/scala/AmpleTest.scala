package pipeline

// TODO(kgeffen) prune
import puppet.syntax._
import puppet.graph._

import puppet.common.{resource => resrc}

import fsmodel._
import fsmodel.ext._

import org.scalatest.FunSuite
import java.nio.file._

class AmpleTest extends FunSuite {

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

  // Takes 13 mins
  test("3 package install") {
    val program = """package{["sl",
                              "cowsay",
                              "cmatrix"]: }"""
    runTest("4.dot", program)
  }

  def runTest(filename: String, program: String) {
    val graph = parse(program).desugar()
                              .toGraph(Map[String, String]())

    val extExpr = pipeline.resourceGraphToExpr(graph)
    val evalGraph = Ample.makeGraph(Ample.initState, extExpr)
    info(s"Graph has ${evalGraph.nodes.size} nodes")
    val finalStates = evalGraph.nodes.filter(n => n.outDegree == 0 && n._2 == Skip).map(_.value._1).take(2)
    // for (p <- finalStates) {
    //   info(p.toString)
    // }
    //l finalStates = Ample.finalStates(Ample.initState, extExpr)
    info(finalStates.size.toString)
    //fo(finalStates.toString)
    Files.write(Paths.get(filename), Ample.drawGraph(extExpr).getBytes)
  }
}
