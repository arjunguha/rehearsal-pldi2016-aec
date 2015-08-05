package parser

import scala.util.parsing.combinator._
import Syntax._

private class Parser extends RegexParsers with PackratParsers {
  type P[+T] = PackratParser[T]


  lazy val bool: P[Atom] = "true" ^^ { _ => ABool(true) } |
                           "false" ^^ { _ => ABool(false) }

  lazy val stringVal: P[String] = "\"" ~> "[^\"]*".r <~ "\"" |
                                  "'" ~> "[^']*".r <~ "'"

  lazy val string: P[Atom] = stringVal ^^ (AString(_))

  lazy val id: P[String] = "" ~> "[a-z_][a-zA-Z0-9_]*".r

  lazy val vari: P[Atom] = "$" ~> id ^^ (AVar(_))

  lazy val symbol: P[Atom] = "present" ^^ (ASymbol(_)) |
                             "absent"  ^^ (ASymbol(_))

  lazy val atom: P[Atom] = bool | symbol | vari | string

  // What is a "word," Puppet? Does it include numbers?
  lazy val attributeName: P[String] = "" ~> "[a-z]+".r

  lazy val attribute: P[Attribute] =
    attributeName ~ ("=>" ~> atom) ^^  { case name ~ value => Attribute(name, value) }

  lazy val attributes: P[Seq[Attribute]] = repsep(attribute, ",")

  // Puppet doesn't tell us what a valid resource type is other than a "word."
  lazy val resourceType: P[String] = "" ~> "[a-zA-Z]+".r

  lazy val resource: P[Expr] = resourceType ~ ("{" ~> stringVal <~ ":") ~ (attributes <~ "}") ^^ {
    case typ ~ name ~ attr => Resource(name, typ, attr)
  }

  lazy val resourceName: P[String] = "" ~> "[a-zA-Z]+".r

  lazy val leftEdge: P[Expr] =
    resourceName ~ ("~>" ~> resourceName) ^^ { case parent ~ child => LeftEdge(parent, child) }

  lazy val rightEdge: P[Expr] =
    resourceName ~ ("<~" ~> resourceName) ^^ { case child ~ parent => RightEdge(parent, child) }

  lazy val edge: P[Expr] = leftEdge | rightEdge

  lazy val expr: P[Expr] = resource | edge

  lazy val prog: P[Seq[Expr]] = rep(expr)

  def parseString[A](expr: String, parser: Parser[A]): A = {
    parseAll(parser, expr) match {
      case Success(r, _) => r
      case m => throw new RuntimeException(s"$m")
    }
  }
}

object Parser {
  private val parser = new Parser()

  def parseAtom(str: String): Atom = parser.parseString(str, parser.atom)
  def parseAttribute(str: String): Attribute = parser.parseString(str, parser.attribute)
  def parseExpr(str: String): Expr = parser.parseString(str, parser.expr)
  def parse(str: String): Seq[Expr] = parser.parseString(str, parser.prog)
}
