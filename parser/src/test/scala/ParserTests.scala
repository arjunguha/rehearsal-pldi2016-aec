import parser.Parser._
import parser.Syntax._

class ParserTestSuite extends org.scalatest.FunSuite {
  test("atoms") {
    assert(parseAtom("true") == ABool(true))
    assert(parseAtom("false") == ABool(false))
    assert(parseAtom("\"string\"") == AString("string"))
    assert(parseAtom("'string'") == AString("string"))
    assert(parseAtom("$foo") == AVar("foo"))
    assert(parseAtom("present") == ASymbol("present"))
  }

  test("attributes") {
    assert(parseAttribute("present => true") == Attribute("present", ABool(true)))
  }

  test("resources") {
    assert(parseExpr("user { 'awe': ensure => present }") == Resource("awe", "user", Seq(Attribute("ensure", ASymbol("present")))))
    assert(parseExpr("user { 'awe': ensure => present, foo => 'bar' }") == Resource("awe", "user", Seq(Attribute("ensure", ASymbol("present")), Attribute("foo", AString("bar")))))
  }

  test("edges") {
    assert(parseExpr("P ~> Q") == LeftEdge("P", "Q"))
    assert(parseExpr("Q <~ P") == RightEdge("P", "Q"))
  }

  test("programs") {
    val prog =
      """
        user { 'awe':
          ensure => present,
          foo => 'bar'
        }
        P ~> Q
        Q <~ P
      """
    val res = Seq(
      Resource("awe", "user", Seq(Attribute("ensure", ASymbol("present")), Attribute("foo", AString("bar")))),
      LeftEdge("P", "Q"),
      RightEdge("P", "Q")
    )
    assert(parse(prog) == res)
  }
}
