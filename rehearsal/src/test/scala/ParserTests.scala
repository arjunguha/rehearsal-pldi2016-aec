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
    assert(parseExpr("File['P'] -> File['Q']") == LeftEdge(ARes("File", "P"), ARes("File", "Q")))
    assert(parseExpr("Package['Q'] <- Package['P']") == 
      RightEdge(ARes("Package", "P"), ARes("Package", "Q")))
  }

  test("defines") {
    assert(parseExpr("""define foo($bar = 'baz') {
      file { 'foo':
        ensure => present,
      }
    }""") == Define("foo", Seq(Argument("bar", "Any", Some(AString("baz")))), Seq(Resource("foo", "file", Seq(Attribute("ensure", ASymbol("present")))))))
  }

  test("programs") {
    val prog =
      """
        user { 'awe':
          ensure => present,
          foo => 'bar'
        }
        Package['P'] -> File['Q']
        File['Q'] <- Package['P']
      """
    val res = Seq(
      Resource("awe", "user", Seq(Attribute("ensure", ASymbol("present")), Attribute("foo", AString("bar")))),
      LeftEdge(ARes("Package", "P"), ARes("File", "Q")),
      RightEdge(ARes("Package", "P"), ARes("File", "Q"))
    )
    assert(parse(prog) == res)
  }

  test("if") {
    val prog = 
      """
        if true {
          user { 'awe':
            ensure => present,
            foo => 'bar'
          }
        } else {
          user { 'awe':
            ensure => present,
            foo => 'bar'
          }          
        }
      """
    val res = Seq(ITE(BAtom(ABool(true)), 
      Seq(Resource("awe", "user", Seq(Attribute("ensure", ASymbol("present")), Attribute("foo", AString("bar"))))),
      Some(Seq(Resource("awe", "user", Seq(Attribute("ensure", ASymbol("present")), Attribute("foo", AString("bar"))))))
    ))
    assert(parse(prog) == res)
  }

  test("class"){
    val prog = 
      """
        class apache (String $version = 'latest'){
            package {'httpd':
              ensure => $version, 
              before => File['/etc/httpd.conf'],
            }
        }
      """
    val res = Seq(Class("apache", Seq(Argument("version", "String", Some(AString("latest")))), 
                        Seq(Resource("httpd", "package", Seq(Attribute("ensure", AVar("version")), 
                                                             Attribute("before", ARes("File", "/etc/httpd.conf")))))))
    assert(parse(prog) == res)
  }
}
