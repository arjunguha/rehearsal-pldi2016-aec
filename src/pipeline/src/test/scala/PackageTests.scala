package pipeline

import org.scalatest.FunSuite

class PackageTestSuite extends FunSuite {

  val env = Facter.emptyEnv
  val fs = Ubuntu.lightweight_fs

  test("single package without attributes") {
    val program = """package{"sl": }"""
    assert(1 == pipeline.runProgram(program, env, fs))
  }

  test("2 package dependent install") {
    val program = """package{"sl": }
                     package{"cmatrix":
                       require => Package['sl']
                     }"""
    assert(1 == pipeline.runProgram(program, env, fs))
  }

  test("2 package concurrent install") {
    val program = """package{["cmatrix",
                              "telnet"]: }"""
    assert(1 == pipeline.runProgram(program, env, fs))
  }

  test("single package remove") {
    val program = """package{"telnet":
                       ensure => absent
                    }"""
    assert(1 == pipeline.runProgram(program, env, fs))
  }

  test("3 packages install") {
    val program = """package{["sl",
                              "cowsay",
                              "cmatrix"]: }"""
    assert(1 == pipeline.runProgram(program, env, fs))
  }
}
