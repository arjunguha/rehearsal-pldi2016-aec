package parser

object Syntax {

	case class Attribute(name: Expr, value: Expr)
	case class Argument(id: String) //ignoring types and default values for now

	sealed trait Manifest
	case object Empty extends Manifest
	case class Block(m1: Manifest, m2: Manifest) extends Manifest
	case class Resource(title: Expr, typ: String, attrs: Seq[Attribute]) extends Manifest
	case class ITE(pred: Expr, m1: Manifest, m2: Manifest) extends Manifest
	case class Edge(m1: Manifest, m2: Manifest) extends Manifest
	case class Define(name: String, params: Seq[Argument], body: Manifest) extends Manifest
	case class Let(varName: String, e: Expr, body: Manifest) extends Manifest
	case class E(e: Expr) extends Manifest

	sealed trait Expr
	case class Str(s: String) extends Expr
	case class Res(typ: String, e: Expr) extends Expr
	case class Var(name: String) extends Expr
	case class Bool(b: Boolean) extends Expr
	case class Not(e: Expr) extends Expr
	case class And(e1: Expr, e2: Expr) extends Expr
	case class Or(e1: Expr, e2: Expr) extends Expr
	case class Eq(e1: Expr, e2: Expr) extends Expr
	case class Match(e1: Expr, e2: Expr) extends Expr
	case class In(e1: Expr, e2: Expr) extends Expr
}