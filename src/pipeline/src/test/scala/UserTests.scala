package pipeline

import org.scalatest.FunSuite

class UserTestSuite extends FunSuite {

  test("single group creation") {
    val program = """group{"thegroup": ensure => present }"""
    assert(1 == pipeline.runProgram(program, Ubuntu.fs_state))
  }

  test("single user creation") {
    val program = """user{"abc": ensure => present }"""
    assert(1 == pipeline.runProgram(program, Ubuntu.fs_state))
  }

  test("concurrent group creation") {
    val program = """group{["a", "b"]: ensure => present }"""
    assert(1 == pipeline.runProgram(program, Ubuntu.fs_state))
  }

  test("concurrent user creation") {
    val program = """user{["abc", "def"]: ensure => present }"""
    assert(1 == pipeline.runProgram(program, Ubuntu.fs_state))
  }

  test("user remove") {
    val program = """user{"abc":
                       ensure => absent
                    }"""
    assert(1 == pipeline.runProgram(program, Ubuntu.fs_state))
  }
}
