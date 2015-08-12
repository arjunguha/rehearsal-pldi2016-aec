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
  case class BAnd(lhs: BoolOps, rhs: BoolOps) extends BoolOps
  case class BOr(lhs: BoolOps, rhs: BoolOps) extends BoolOps
  case class BNot(arg: BoolOps) extends BoolOps
  case class BEq(lhs: BoolOps, rhs: BoolOps) extends BoolOps
  case class BNEq(lhs: BoolOps, rhs: BoolOps) extends BoolOps
  case class BMatch(lhs: BoolOps, rhs: BoolOps) extends BoolOps
  case class BNMatch(lhs: BoolOps, rhs: BoolOps) extends BoolOps
  case class BIn(lhs: BoolOps, rhs: BoolOps) extends BoolOps

  sealed trait Manifest
  case object EmptyExpr extends Manifest
  case class Block(e1: Manifest, e2: Manifest) extends Manifest
  case class Resource(id: Atom, typ: String, attributes: Seq[Attribute]) extends Manifest
  case class Edge(parent: ARes, child: ARes) extends Manifest
  case class Define(name: String, args: Seq[Argument], body: Manifest) extends Manifest
  case class ITE(pred: BoolOps, thn: Manifest, els: Manifest) extends Manifest
  case class Class(name: String, parameters: Seq[Argument], body: Manifest) extends Manifest

  def simplifyAttributes(lst: Seq[Attribute], src: ARes): (Seq[Attribute], Manifest) = {
    lst.foldRight[(Seq[Attribute], Manifest)]((Seq(), EmptyExpr)) {
      case (Attribute("before", res@ARes(_, _)), (attrs, expr)) => (attrs, Block(Edge(src, res), expr))
      case (Attribute("require", res@ARes(_, _)), (attrs, expr)) => (attrs, Block(Edge(res, src), expr))
      case (attr, (attrs, expr)) => (attr +: attrs, expr)
    }
  }

  def desugar(expr: Manifest): Manifest = expr match {
    case EmptyExpr => EmptyExpr
    case Block(e1, e2) => Block(desugar(e1), desugar(e2))
    case Resource(AString(id), typ, attrs) => simplifyAttributes(attrs, ARes(typ.capitalize, id)) match {
      case (attrs, expr) => Block(Resource(AString(id), typ, attrs), expr)
    }
    case Resource(id, typ, attrs) => simplifyAttributes(attrs, ARes(typ.capitalize, "__" + id.toString + "__")) match {
      case (attrs, expr) => Block(Resource(id, typ, attrs), expr)
    }
    case Define(name, args, body) => Define(name, args, desugar(body))
    case ITE(pred, thn, els) => ITE(pred, desugar(thn), desugar(els))
    case Class(name, parameters, body) => Class(name, parameters, desugar(body))
    case edge@Edge(_, _) => edge
  }
}
