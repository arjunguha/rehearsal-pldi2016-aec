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
	lazy val manifest: P[Manifest] = edge | let | define | resource | ite | exprMan

	lazy val body: P[Manifest] = "{" ~> prog <~ "}"

	lazy val parameter: P[Argument] = opt(dataType) ~ varName ~ opt("=" ~> expr) ^^ {
		case Some(typ) ~ id ~ default => Argument(id)
		case None ~ id ~ default => Argument(id)
	}

	lazy val parameters: P[Seq[Argument]] = "(" ~> repsep(parameter, ",") <~ ")"

	lazy val resource: P[Manifest] = word ~ ("{" ~> expr <~ ":") ~ (attributes <~ "}") ^^ {
		case typ ~ id ~ attr => Resource(id, typ, attr)
	}

	lazy val ite: P[Manifest] = "if" ~> (bop | vari) ~ body ~ rep(elsif) ~ opt("else" ~> body) ^^ {
		case pred ~ thn ~ elsifs ~ els => ITE(pred, thn, elsifs.foldRight(els.getOrElse(Empty)) {
			case ((pred, body), acc) => ITE(pred, body, acc)
		})
	}

	lazy val elsif: P[(Expr, Manifest)] = "elsif" ~> bop ~ body ^^ { case pred ~ body => (pred, body) }

	lazy val edge: P[Manifest] = 
		manifest ~ ("->" ~> manifest) ^^ { case parent ~ child => Edge(parent, child) } |
		manifest ~ ("<-" ~> manifest) ^^ { case child ~ parent => Edge(parent, child) }

	lazy val define: P[Manifest] = "define" ~> word ~ opt(parameters) ~ body ^^ {
		case name ~ Some(args) ~ body => Define(name, args, body)
		case name ~ None ~ body => Define(name, Seq(), body)
	}

	lazy val let: P[Manifest] = varName ~ ("=" ~> expr) ~ opt(manifest) ^^ 
								{ case id ~ e ~ body => Let(id, e, body.getOrElse(Empty)) }

	//Attribute
	lazy val argument: P[Var] = id ^^ { Var(_) } //used for passing arguments to defined types
	lazy val attribute: P[Attribute] = 
		(expr | argument) ~ ("=>" ~> expr) ^^ { case name ~ value => Attribute(name, value) }

	lazy val attributes: P[Seq[Attribute]] = repsep(attribute, ",") <~ opt(",")

	//Expr
	lazy val exprMan: P[Manifest] = expr ^^ (E(_))

	lazy val expr: P[Expr] = res | vari | bool | string | bop

	lazy val res: P[Expr] = word ~ ("[" ~> expr <~ "]") ^^ { case typ ~ e => Res(typ, e) }

	lazy val vari: P[Expr] = varName ^^ (Var(_))

	//Operators
	lazy val atom = bool | res | vari | string
	lazy val batom = not | bool 

	lazy val not: P[Expr] = ("!" ~> expr) ^^ { Not(_) }

	lazy val and: P[Expr] = and ~ ("and" ~> batom) ^^ { case lhs ~ rhs => And(lhs, rhs) } | batom

	lazy val or: P[Expr] = or ~ ("or" ~> and) ^^ { case lhs ~ rhs => Or(lhs, rhs) } | and

	lazy val bop: P[Expr] = 	(bop | atom) ~ ("==" ~> (or | atom)) ^^ { case lhs ~ rhs => Eq(lhs, rhs) } |
							(bop | atom) ~ ("!=" ~> (or | atom)) ^^ { case lhs ~ rhs => Not(Eq(lhs, rhs)) } |
							(bop | atom) ~ ("=~" ~> (or | atom)) ^^ { case lhs ~ rhs => Match(lhs, rhs) } |
							(bop | atom) ~ ("!~" ~> (or | atom)) ^^ { case lhs ~ rhs => Not(Match(lhs, rhs)) } |
							(bop | atom) ~ ("in" ~> (or | atom)) ^^ { case lhs ~ rhs => In(lhs, rhs) } |
							or

	//Constants
	lazy val bool: P[Expr] = "true" ^^ { _ => Bool(true) } |
								"false" ^^ { _ => Bool(false) }

	lazy val string: P[Str] = stringVal ^^ (Str(_))

	// def desugarAttrs(r: Resource, attrs: Seq[Attribute]): Manifest = (r, attrs) match {
	// 	case (_, Seq()) => r
	// 	case (Resource(name, typ, _), Attribute(Str("before"), child)::t) => 
	// 		Block(desugarAttrs(Resource(name, typ, t), t), Edge(r, E(child)))
	// 	case (Resource(name, typ, _), Attribute(Str("require"), child)::t) => 
	// 		Block(desugarAttrs(Resource(name, typ, t), t), Edge(E(child), r))
	// 	case _ => r
	// }

	// def desugarAttrs(r: Resource, attrs: Seq[Attribute]): (Seq[Attribute], Manifest) = (r, attrs) match {
	// 	case (_, Seq()) => (Seq(), Empty)
	// 	case (_, Attribute(Str("before"), child) :: t) => 
	// 	case (_, Attribute(Str("require"), parent) :: t) => 
	// 	case _ => (attrs, Empty)
	// }	
	
	// def desugar(m: Manifest): Manifest = m match {
		
	// }

	def simplifyAttributes(lst: Seq[Attribute], src: Res): (Seq[Attribute], Manifest) = {
		lst.foldRight[(Seq[Attribute], Manifest)]((Seq(), Empty)) {
			case (Attribute(Str("before"), res), (attrs, m)) => (attrs, Block(Edge(E(src), E(res)), m))
			case (Attribute(Str("require"), res), (attrs, m)) => (attrs, Block(Edge(E(res), E(src)), m))
			case (attr, (attrs, m)) => (attr +: attrs, m)
		}
	}

	def desugar(m: Manifest): Manifest = m match {
		case Empty => Empty
		case Block(e1, e2) => Block(desugar(e1), desugar(e2))
		case Resource(Str(id), typ, attrs) => simplifyAttributes(attrs, Res(typ.capitalize, Str(id))) match {
			case (attrs, Empty) => Resource(Str(id), typ, attrs)
			case (attrs, m) => Block(Resource(Str(id), typ, attrs), m)
		}
		case Resource(id, typ, attrs) => simplifyAttributes(attrs, Res(typ.capitalize, id)) match {
			case (attrs, Empty) => Resource(id, typ, attrs)
			case (attrs, m) => Block(Resource(id, typ, attrs), m)
		}
		case Let(id, value, body) => Let(id, value, desugar(body))
		case Define(name, args, body) => Define(name, args, desugar(body))
		case ITE(pred, thn, els) => ITE(pred, desugar(thn), desugar(els))
		case E(_) => m
		case Edge(_, _) => m
	}
	
	//Program
	lazy val prog: P[Manifest] = rep(manifest) ^^ { case exprs => blockExprs(exprs) }

	def blockExprs(exprs: Seq[Manifest]): Manifest = exprs.init match {
		case Seq() => exprs.last
		case init => init.foldRight[Manifest](exprs.last) {
			case (e1, e2) => Block(e1, e2)
		}
	}

	def parseString[A](expr: String, parser: Parser[A]): A = {
		parseAll(parser, expr) match{
			case Success(r, _) => r
			case m => throw new RuntimeException(s"$m")
		}
	}	
}

object Parser2 {
	private val parser = new Parser2()

	def parseBool(str: String): Expr = parser.parseString(str, parser.bool)
	def parseStr(str: String): Str = parser.parseString(str, parser.string)
	def parseOps(str: String): Expr = parser.parseString(str, parser.bop)
	def parseExpr(str: String): Expr = parser.parseString(str, parser.expr)
	def parseAttribute(str: String): Attribute = parser.parseString(str, parser.attribute)
	def parseArgument(str: String): Argument = parser.parseString(str, parser.parameter)
	def parseManifest(str: String): Manifest = parser.parseString(str, parser.manifest)
	def parse(str: String): Manifest = parser.desugar(parser.parseString(str, parser.prog))
}