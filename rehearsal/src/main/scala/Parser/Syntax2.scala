package parser

object Syntax2 {

	case class Attribute(name: Expr, value: Expr)
	case class Argument(id: String) //ignoring types and default values for now

	sealed trait Manifest
	case object Empty extends Manifest
	case class Block(m1: Manifest, m2: Manifest) extends Manifest
	case class Resource(typ: String, attrs: Seq[Attribute]) extends Manifest
	case class ITE(pred: Expr, m1: Manifest, m2: Manifest) extends Manifest
	case class Edge(m1: Manifest, m2: Manifest) extends Manifest
	case class Define(name: String, params: Seq[Argument], body: Manifest) extends Manifest
	case class Let(varName: String, e: Expr, body: Manifest) extends Manifest
	case class E(e: Expr) extends Manifest

	sealed trait Expr
	case class Str(s: String) extends Expr
	case class Res(typ: String, e: Expr) extends Expr
	case class Var(name: String) extends Expr

	sealed trait Pred extends Expr
	case class Bool(b: Boolean) extends Pred	

	//Unary operators
	sealed trait Op1 extends Pred
	case class Not(e: Expr) extends Op1

	//binary operators
	sealed trait Op2 extends Pred
	case class And(e1: Expr, e2: Expr) extends Op2
	case class Or(e1: Expr, e2: Expr) extends Op2
	case class Eq(e1: Expr, e2: Expr) extends Op2
	case class Match(e1: Expr, e2: Expr) extends Op2
	case class In(e1: Expr, e2: Expr) extends Op2
}