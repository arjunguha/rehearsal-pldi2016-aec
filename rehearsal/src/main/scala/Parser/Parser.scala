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

  lazy val varName: P[String] =  "$" ~> id

  lazy val vari: P[Atom] = varName ^^ (AVar(_))

  lazy val symbol: P[Atom] = "present" ^^ (ASymbol(_)) |
                             "absent"  ^^ (ASymbol(_))

  lazy val resAtom: P[ARes] = 
    resourceType ~ ("[" ~> stringVal <~ "]") ^^ { case typ ~ id => ARes(typ, id) }

  lazy val atom: P[Atom] = bool | resAtom | symbol | vari | string

  // What is a "word," Puppet? Does it include numbers?
  lazy val attributeName: P[String] = "" ~> "[a-z]+".r

  lazy val attribute: P[Attribute] =
    attributeName ~ ("=>" ~> atom) ^^ { case name ~ value => Attribute(name, value) }

  lazy val attributes: P[Seq[Attribute]] = repsep(attribute, ",") <~ opt(",")

  // Puppet doesn't tell us what a valid resource type is other than a "word."
  lazy val resourceType: P[String] = "" ~> "[a-zA-Z]+".r

  lazy val resource: P[Expr] = resourceType ~ ("{" ~> stringVal <~ ":") ~ (attributes <~ "}") ^^ {
    case typ ~ name ~ attr => Resource(name, typ, attr)
  }

  lazy val resourceName: P[String] = "" ~> "[a-zA-Z]+".r

  lazy val leftEdge: P[Expr] =
    resAtom ~ ("->" ~> resAtom) ^^ { case parent ~ child => LeftEdge(parent, child) }

  lazy val rightEdge: P[Expr] =
    resAtom ~ ("<-" ~> resAtom) ^^ { case child ~ parent => RightEdge(parent, child) }

  lazy val edge: P[Expr] = leftEdge | rightEdge

  lazy val dataType: P[String] = "" ~> "[A-Z][a-zA-Z]+".r

  lazy val argument: P[Argument] = opt(dataType) ~ varName ~ opt("=" ~> atom) ^^ {
    case Some(typ) ~ id ~ default => Argument(id, typ, default)
    case None ~ id ~ default => Argument(id, "Any", default)
  }

  lazy val arguments: P[Seq[Argument]] = "(" ~> repsep(argument, ",") <~ ")"

  lazy val define = "define" ~> resourceType ~ opt(arguments) ~ ("{" ~> prog <~ "}") ^^ {
    case name ~ Some(args) ~ body => Define(name, args, body)
    case name ~ None ~ body => Define(name, Seq(), body)
  }

  lazy val expr: P[Expr] = define | resource | edge

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
