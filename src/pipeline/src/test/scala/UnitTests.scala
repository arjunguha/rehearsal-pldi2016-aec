import org.scalatest.FunSuite

import pipeline.main._

class UnitTestSuite extends FunSuite {

  test("single puppet file resource") {
    Pipeline.runPipeline("""file{"/foo": ensure => present }""")
  }

  test("single directory") {
    Pipeline.runPipeline("""file{"/tmp":
                              ensure => directory
                            }""")
  }

  test("file inside a directory") {
    Pipeline.runPipeline("""file{"/tmp/foo":
                              ensure => present,
                              require => File['/tmp']
                            }
                            file{"/tmp":
                              ensure => directory
                            }""")
  }
}
