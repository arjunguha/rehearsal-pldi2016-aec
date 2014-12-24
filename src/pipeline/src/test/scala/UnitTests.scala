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

  test("single puppet file resource with force") {
    Pipeline.runPipeline("""file{"/foo":
                              ensure => file,
                              force => true
                            }""")
  }

  test("delete file resource") {
    Pipeline.runPipeline("""file{"/foo": ensure => absent }""")
  }

  test("delete dir with force") {
    Pipeline.runPipeline("""file {"/tmp":
                              ensure => absent,
                              force => true
                            }""")
  }

  test("link file") {
    Pipeline.runPipeline("""file{"/foo":
                              ensure => link,
                              target => "/bar"
                            }""")
  }

  test("link file force") {
    Pipeline.runPipeline("""file{"/foo":
                              ensure => link,
                              target => "/bar",
                              force => true
                            }""")
  }
}
