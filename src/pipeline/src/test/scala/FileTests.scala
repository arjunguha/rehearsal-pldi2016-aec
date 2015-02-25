package pipeline

import org.scalatest.FunSuite

class FileTestSuite extends FunSuite {

  test("single puppet file resource") {
    pipeline.runProgram("""file{"/foo": ensure => present }""")
  }

  test("single directory") {
    pipeline.runProgram("""file{"/tmp":
                              ensure => directory
                            }""")
  }

  test("file inside a directory") {
    pipeline.runProgram("""file{"/tmp/foo":
                              ensure => present,
                              require => File['/tmp']
                            }
                            file{"/tmp":
                              ensure => directory
                            }""")
  }

  test("single puppet file resource with force") {
    pipeline.runProgram("""file{"/foo":
                              ensure => file,
                              force => true
                            }""")
  }

  test("delete file resource") {
    pipeline.runProgram("""file{"/foo": ensure => absent }""")
  }

  test("delete dir with force") {
    pipeline.runProgram("""file {"/tmp":
                              ensure => absent,
                              force => true
                            }""")
  }

  test("link file") {
    pipeline.runProgram("""file{"/foo":
                              ensure => link,
                              target => "/bar"
                            }""")
  }

  test("link file force") {
    pipeline.runProgram("""file{"/foo":
                              ensure => link,
                              target => "/bar",
                              force => true
                            }""")
  }
}
