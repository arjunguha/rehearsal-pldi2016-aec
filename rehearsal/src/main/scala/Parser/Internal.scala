package parser

object Internal {
  case class Attribute(name: String, value: Atom)
  case class Argument(id: String, typ: String, default: Option[Atom])

  sealed trait Atom
  case class ASymbol(name: String) extends Atom
  case class ABool(value: Boolean) extends Atom
  case class AString(value: String) extends Atom
  case class AVar(id: String) extends Atom
  case class ARes(typ: String, id: String) extends Atom

  sealed trait BoolOps
  case class BAtom(atom: Atom) extends BoolOps
  case class BNAnd(lhs: BoolOps, rhs: BoolOps) extends BoolOps
  case class BEq(lhs: BoolOps, rhs: BoolOps) extends BoolOps
  case class BNEq(lhs: BoolOps, rhs: BoolOps) extends BoolOps
  case class BMatch(lhs: BoolOps, rhs: BoolOps) extends BoolOps
  case class BNMatch(lhs: BoolOps, rhs: BoolOps) extends BoolOps
  case class BIn(lhs: BoolOps, rhs: BoolOps) extends BoolOps

  sealed trait Expr
  case class Resource(id: Atom, typ: String, attributes: Seq[Attribute]) extends Expr
  case class Edge(parent: ARes, child: ARes) extends Expr
  case class Define(name: String, args: Seq[Argument], body: Seq[Expr]) extends Expr
  case class ITE(pred: BoolOps, thn: Seq[Expr], els: Option[Seq[Expr]]) extends Expr
  case class Class(name: String, parameters: Seq[Argument], body: Seq[Expr]) extends Expr

  def simplifyAttributes(lst: Seq[Attribute], src: ARes): (Seq[Attribute], Seq[Expr]) = 
  	lst.foldRight[(Seq[Attribute], Seq[Expr])]((Seq(), Seq())) {
  		case (Attribute("before", res@ARes(_, _)), (attrs, exprs)) => (attrs, Edge(src, res) +: exprs)
  		case (Attribute("require", res@ARes(_, _)), (attrs, exprs)) => (attrs, Edge(res, src) +: exprs)
  		case (attr, (attrs, exprs)) => (attr +: attrs, exprs)
  	}

  def desugar(lst: Seq[Expr]): Seq[Expr] = 
  	lst.foldRight[Seq[Expr]](Seq()) {
  		case (Resource(AString(id), typ, attrs), acc) => simplifyAttributes(attrs, ARes(typ.capitalize, id)) match {
  			case (attrs, exprs) => Resource(AString(id), typ, attrs) +: (exprs ++ acc)
  		}
  		case (Resource(id, typ, attrs), acc) => simplifyAttributes(attrs, ARes(typ.capitalize, "__" + id.toString + "__")) match {
  			case (attrs, exprs) => Resource(id, typ, attrs) +: (exprs ++ acc)
  		}
  		case (Define(name, args, body), acc) => Define(name, args, desugar(body)) +: acc
  		case (ITE(pred, thn, els), acc) => ITE(pred, desugar(thn), els.map(desugar)) +: acc
  		case (Class(name, parameters, body), acc) => Class(name, parameters, desugar(body)) +: acc
  		case (edge@Edge(_, _), acc) => edge +: acc 
  	}

}
