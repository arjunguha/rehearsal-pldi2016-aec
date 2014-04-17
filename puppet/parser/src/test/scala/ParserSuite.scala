import org.scalatest._

class ParserSpec extends FunSuite {

  test("basic test") {
    assert(PuppetParser("$a = / 4").successful == false)

  }

}