package parser

import scala.util.parsing.combinator._
import Syntax2._

private class Parser2 extends RegexParsers with PackratParsers{
	type P[+T] = PackratParser[T]

	lazy val stringVal: P[String] = "\"" ~> "[^\"]*".r <~ "\"" |
									"'" ~> "[^']*".r <~ "'"
	lazy val word: P[String] = "" ~> "[a-zA-Z]+".r

	//Manifest

	//Expr
	lazy val expr: P[Expr] = res | vari | constant | op1 | op2

	lazy val res: P[Expr] = 

	//Operators
	lazy val op1: P[Op1] = not
	lazy val op2: P[Op2] = and | or | bop

	lazy val not: P[Op1] = ("!" ~> expr) ^^ { Not(_) }

	lazy val and: P[Op2] = and ~ ("and" ~> expr) ^^ { case lhs ~ rhs => And(lhs, rhs) } | expr

	lazy val or: P[Op2] = or ~ ("or" ~> and) ^^ { case lhs ~ rhs => Or(lhs, rhs) } | and

	lazy val bop: P[Op2] = 	bop ~ ("==" ~> or) ^^ { case lhs ~ rhs => Eq(lhs, rhs) } |
                           	bop ~ ("!=" ~> or) ^^ { case lhs ~ rhs => Not(Eq(lhs, rhs)) } |
                           	bop ~ ("=~" ~> or) ^^ { case lhs ~ rhs => Match(lhs, rhs) } |
                           	bop ~ ("!~" ~> or) ^^ { case lhs ~ rhs => Not(Match(lhs, rhs)) } |
                           	bop ~ ("in" ~> or) ^^ { case lhs ~ rhs => In(lhs, rhs) } |
                           	or

	//Constants
	lazy val constant: P[Constant] = bool | string

	lazy val bool: P[Constant] = "true" ^^ { _ => Bool(true) } |
								"false" ^^ { _ => Bool(false) }

	lazy val string: P[Constant] = stringVal ^^ (Str(_))

}