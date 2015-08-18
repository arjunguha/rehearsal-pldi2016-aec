package parser

import scala.util.parsing.combinator._
import Syntax2._

private class Parser2 extends RegexParsers with PackratParsers{
	type P[+T] = PackratParser[T]

	lazy val stringVal: P[String] = "\"" ~> "[^\"]*".r <~ "\"" |
									"'" ~> "[^']*".r <~ "'"
	lazy val word: P[String] = "" ~> "[a-zA-Z]+".r
	lazy val id: P[String] = "" ~> "[a-z_][a-zA-Z0-9_]*".r
	lazy val attributeName: P[String] = "" ~> "[a-z]+".r
	lazy val dataType: P[String] = "" ~> "[A-Z][a-zA-Z]+".r
	lazy val varName: P[String] =  "$" ~> id

	//Manifest
	lazy val manifest: P[Manifest] = block |/* let | define | */resource | /*edge |*/ ite 

	lazy val body: P[Manifest] = "{" ~> expr <~ "}"

	lazy val argument: P[Argument] = opt(dataType) ~ varName ~ opt("=" ~> expr) ^^ {
		case Some(typ) ~ id ~ default => Argument(id)
		case None ~ id ~ default => Argument(id)
	}

	lazy val arguments: P[Seq[Argument]] = "(" ~> repsep(argument, ",") <~ ")"

	lazy val block: P[Manifest] = rep(expr) ^^ { case exprs => exprs.init match {
			case Seq() => exprs.last
			case init => init.foldRight[Manifest](exprs.last) {
				case(e1, e2) => Block(e1, e2)
			}
		} 
	}

	lazy val resource: P[Manifest] = word ~ ("{" ~> expr <~ ":") ~ (attributes <~ "}") ^^ {
		case typ ~ id ~ attr => Resource(typ, attr)
	}

	lazy val ite: P[Manifest] = "if" ~> bop ~ body ~ rep(elsif) ~ opt("else" ~> body) ^^ {
		case pred ~ thn ~ elsifs ~ els => ITE(pred, thn, elsifs.foldRight(els.getOrElse(Empty)) {
			case ((pred, body), acc) => ITE(pred, body, acc)
		})
	}

	lazy val elsif: P[(Expr, Manifest)] = "elsif" ~> bop ~ body ^^ { case pred ~ body => (pred, body) }

	lazy val edge: P[Manifest] = 
		manifest ~ ("->" ~> manifest) ^^ { case parent ~ child => Edge(parent, child) } |
		manifest ~ ("<-" ~> manifest) ^^ { case child ~ parent => Edge(parent, child) }

	lazy val define: P[Manifest] = "define" ~> word ~ opt(arguments) ~ body ^^ {
		case name ~ Some(args) ~ body => Define(name, args, body)
		case name ~ None ~ body => Define(name, Seq(), body)
	}

	lazy val let: P[Manifest] = varName ~ ("=" ~> expr) ~ opt(manifest) ^^ 
								{ case id ~ e ~ body => Let(id, e, body.getOrElse(Empty)) }

	//Attribute
	lazy val attribute: P[Attribute] = 
		expr ~ ("=>" ~> expr) ^^ { case name ~ value => Attribute(name, value) }

	lazy val attributes: P[Seq[Attribute]] = repsep(attribute, ",") <~ opt(",")

	//Expr
	lazy val expr: P[Expr] = res | vari | constant | op1 | op2 | nbop

	lazy val res: P[Expr] = word ~ ("[" ~> expr <~ "]") ^^ { case typ ~ e => Res(typ, e) }

	lazy val vari: P[Expr] = varName ^^ (Var(_))

	//Operators
	lazy val op1: P[Op1] = not
	lazy val op2: P[Op2] = and | or | bop

	lazy val not: P[Op1] = ("!" ~> expr) ^^ { Not(_) }

	lazy val and: P[Op2] = and ~ ("and" ~> expr) ^^ { case lhs ~ rhs => And(lhs, rhs) } 

	lazy val or: P[Op2] = or ~ ("or" ~> and) ^^ { case lhs ~ rhs => Or(lhs, rhs) } | and

	lazy val bop: P[Op2] = 	bop ~ ("==" ~> or) ^^ { case lhs ~ rhs => Eq(lhs, rhs) } |
                           	bop ~ ("=~" ~> or) ^^ { case lhs ~ rhs => Match(lhs, rhs) } |
                           	bop ~ ("in" ~> or) ^^ { case lhs ~ rhs => In(lhs, rhs) } |
                           	or

    lazy val nbop: P[Expr] = bop ~ ("!=" ~> or) ^^ { case lhs ~ rhs => Not(Eq(lhs, rhs)) } |
    						bop ~ ("!~" ~> or) ^^ { case lhs ~ rhs => Not(Match(lhs, rhs)) }

	//Constants
	lazy val constant: P[Constant] = bool | string

	lazy val bool: P[Constant] = "true" ^^ { _ => Bool(true) } |
								"false" ^^ { _ => Bool(false) }

	lazy val string: P[Constant] = stringVal ^^ (Str(_))

}