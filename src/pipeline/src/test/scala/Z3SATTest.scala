package pipeline

// TODO(kgeffen) prune
import puppet.syntax._
import puppet.graph._

import puppet.common.{resource => resrc}

import scalax.collection.Graph
import scalax.collection.GraphEdge._
import scalax.collection.GraphPredef._
import scalax.collection.edge.Implicits._

import fsmodel._
import fsmodel.ext._
//

import org.scalatest.FunSuite
import fsmodel.core.Z3Eval._
import fsmodel.core.Z3Eval.z._
import java.nio.file.Paths

class Z3SATTest extends FunSuite {

  test("single package without attributes") {
    val program = """package{"sl": }"""
    runTest(program)
  }

  test("2 package dependent install") {
    val program = """package{"sl": }
                     package{"cmatrix":
                       require => Package['sl']
                     }"""
    runTest(program)
  }

  test("2 package install") {
    val program = """package{["cmatrix",
                              "telnet"]: }"""
    runTest(program)
  }

  // Takes 13 mins
  test("3 package install") {
    val program = """package{["sl",
                              "cowsay",
                              "fortune"]: }"""
    runTest(program)
  }

  def runTest(program: String) {
    val graph = parse(program).desugar()
                              .toGraph(Map[String, String]())

    val ext_expr = pipeline.resourceGraphToExpr(graph)
    info(ext_expr.pretty())

    val core_expr = ext_expr.unconcurOpt()
                           .unatomic()
                           .toCore()

    assert(Some(true) ==
      checkSAT(evalR(core_expr,
                     setFileState(path(Paths.get("/")),
                                  isDir,
                                  newState),
                     newState)))
  }
}
