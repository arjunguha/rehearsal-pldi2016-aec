import org.scalatest._
import puppet._

class ParserSpec extends FunSuite {

  test("basic test") {
    assert(PuppetParser("$a = / 4").successful == false)

  }
}
