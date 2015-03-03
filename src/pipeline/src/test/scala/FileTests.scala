package pipeline

import org.scalatest.FunSuite

class FileTestSuite extends FunSuite {

  val env = Facter.emptyEnv
  val fs = Ubuntu.lightweight_fs

  test("single puppet file resource") {
    val program = """file{"/foo": ensure => present }"""
    assert(1 == pipeline.runProgram(program, env, fs))
  }

  test("single directory") {
    val program = """file{"/tmp":
                              ensure => directory
                            }"""
    assert(1 == pipeline.runProgram(program, env, fs))
  }

  test("file inside a directory") {
    val program = """file{"/tmp/foo":
                       ensure => present,
                       require => File['/tmp']
                     }
                     file{"/tmp":
                       ensure => directory
                     }"""
    assert(1 == pipeline.runProgram(program, env, fs))
  }

  test("single puppet file resource with force") {
    val program = """file{"/foo":
                       ensure => file,
                       force => true
                     }"""
    assert(1 == pipeline.runProgram(program, env, fs))
  }

  test("delete file resource") {
    val program = """file{"/foo": ensure => absent }"""
    assert(1 == pipeline.runProgram(program, env, fs))
  }

  test("delete dir with force") {
    val program = """file {"/tmp":
                       ensure => absent,
                       force => true
                     }"""
    assert(1 == pipeline.runProgram(program, env, fs))
  }

  test("link file") {
    val program = """file{"/foo":
                       ensure => link,
                       target => "/bar"
                     }"""
    assert(1 == pipeline.runProgram(program, env, fs))
  }

  test("link file force") {
    val program = """file{"/foo":
                       ensure => link,
                       target => "/bar",
                       force => true
                     }"""
    assert(1 == pipeline.runProgram(program, env, fs))
  }
}
