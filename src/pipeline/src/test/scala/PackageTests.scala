package pipeline

import org.scalatest.FunSuite 

class PackageTestSuite extends FunSuite {

  test("single package without attributes") {
    val program = """package{"sl": }"""
    assert(1 == pipeline.runProgram(program, Ubuntu.fs_state))
  }

  test("2 package dependent install") {
    val program = """package{"sl": }
                     package{"cmatrix":
                       require => Package['sl']
                     }"""
    assert(1 == pipeline.runProgram(program, Ubuntu.fs_state))
  }

  test("2 package concurrent install") {
    val program = """package{["cmatrix",
                              "telnet"]: }"""
    assert(1 == pipeline.runProgram(program, Ubuntu.fs_state))
  }

  test("single package remove") {
    val program = """package{"telnet":
                       ensure => absent
                    }"""
    assert(1 == pipeline.runProgram(program, Ubuntu.fs_state))
  }

  test("3 packages install") {
    val program = """package{["sl",
                              "cowsay",
                              "fortune"]: }"""
    assert(1 == pipeline.runProgram(program, Ubuntu.fs_state))
  }
}
