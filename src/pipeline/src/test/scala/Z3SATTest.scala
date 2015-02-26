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

class PackageZ3TestSuite extends FunSuite {

  test("single package without attributes") {
    val program = """package{"sl": }"""

    val graph = parse(program).desugar()
                              .toGraph(Facter.run())
    val ext_expr = pipeline.resourceGraphToExpr(graph)

    val core_expr = ext_expr.unconcurOpt()
                           .unatomic()
                           .toCore()

    assert(Some(true) ==
      checkSAT(evalR(core_expr,
                     setFileState(path(Paths.get("/")),
                                  isDir,
                                  newState), // TODO(kgeffen) Set root to isDir
                     newState)))
  }

  /*
  test("2 package dependent install") {
    val program = """package{"sl": }
                     package{"cmatrix":
                       require => Package['sl']
                     }"""
    assert(1 == pipeline.runProgram(program))
  }

  test("2 packages install") {
    val program = """package{["cmatrix",
                              "telnet"]: }"""
    assert(1 == pipeline.runProgram(program))
  }
  */

  /*
  test("3 packages install") {
    val program = """package{["sl",
                              "cowsay",
                              "fortune"]: }"""
    assert(1 == pipeline.runProgram(program))
  }
  */
}
