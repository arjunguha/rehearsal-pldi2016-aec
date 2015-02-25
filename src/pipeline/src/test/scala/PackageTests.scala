package pipeline

import org.scalatest.FunSuite 

class PackageTestSuite extends FunSuite {

  test("single package without attributes") {
    pipeline.runProgram("""package{"sl": }""")
  }
}
