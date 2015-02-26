package pipeline

import org.scalatest.FunSuite 

class PackageTestSuite extends FunSuite {

  test("single package without attributes") {
    val program = """package{"sl": }"""

    val graph = parse(program).desugar()
                              .toGraph(Facter.run())
    val ext_expr = resourceGraphToExpr(graph)

    val core_expr = ext_expr.unconcurOpt()
                           .unatomic()
                           .toCore()

    assert(Some(True) == CheckSAT(core_expr))
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
