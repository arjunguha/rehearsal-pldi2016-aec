import org.scalatest.FunSuite
import puppet.parser._

class ParserUnitTests extends FunSuite {

  test("a node may not appear in a class") {
    intercept[PuppetParserException] {
      val txt = """
        class myClass {
          node 'my-node' {
          }
        }
      """
      PuppetParser(txt)
    }
  }

  test("a node may appear at the top level") {
    val txt = """
      node 'my-node' {
        package{ vim: ensure => present }
      }
    """
    PuppetParser(txt)
  }

}