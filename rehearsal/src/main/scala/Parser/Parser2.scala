package parser

import scala.util.parsing.combinator._
import Syntax2._

private class Parser2 extends RegexParsers with PackratParsers{
	type P[+T] = PackratParser[T]

	lazy val stringVal: P[String] = "\"" ~> "[^\"]*".r <~ "\"" |
									"'" ~> "[^']*".r <~ "'"

	//Manifest

	//Expr
	lazy val expr: P[Expr] = res | vari | constant | op1 | op2

	//Operators
	lazy val op1: P[Op1] = not
	lazy val op2: P[Op2] = and | or | eq | mat | bin

	lazy val not: P[Op1] = ("!" ~> expr) ^^ { Not(_) }

	lazy val and: P[Op2] = and ~ ("and" ~> expr) ^^ { case lhs ~ rhs => And(lhs, rhs) } | expr

	//Constants
	lazy val bool: P[Constant] = "true" ^^ { _ => Bool(true) } |
								"false" ^^ { _ => Bool(false) }

	lazy val string: P[Constant] = stringVal ^^ (Str(_))

}