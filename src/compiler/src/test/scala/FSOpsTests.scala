import org.scalatest.FunSuite

import puppet.driver.{PuppetDriver => driver}

class FSOpsSuite extends FunSuite {

  test(s"verify") {
    val mainFilePath = "./compiler/example/fsops/ex1.pp"
    val modulePath = None
    val content = driver.prepareContent(mainFilePath, modulePath)
    val graph = driver.compile(content)
    driver.verify(graph)
  }
}
