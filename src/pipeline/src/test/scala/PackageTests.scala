package pipeline

import org.scalatest.FunSuite 

class PackageTestSuite extends FunSuite {

  test("single package without attributes") {
    val program = """package{"sl": }"""
    assert(1 == pipeline.runProgram(program))
  }
}
