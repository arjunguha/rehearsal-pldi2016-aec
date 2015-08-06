package parser

object Syntax {
  case class Attribute(name: String, value: Atom)
  case class Argument(id: String, typ: String, default: Option[Atom])

  sealed trait Atom
  case class ASymbol(name: String) extends Atom
  case class ABool(value: Boolean) extends Atom
  case class AString(value: String) extends Atom
  case class AVar(id: String) extends Atom
  case class ARes(typ: String, id: String) extends Atom

  sealed trait BoolOps
  case class BAtom (atom: Atom) extends BoolOps
  case class BAnd(lhs: BoolOps, rhs: BoolOps) extends BoolOps
  case class BOr(lhs: BoolOps, rhs: BoolOps) extends BoolOps
  case class BNot (arg: BoolOps) extends BoolOps
  case class BEq (lhs: BoolOps, rhs: BoolOps) extends BoolOps
  case class BNEq (lhs: BoolOps, rhs: BoolOps) extends BoolOps
  case class BMatch (lhs: BoolOps, rhs: BoolOps) extends BoolOps
  case class BNMatch (lhs: BoolOps, rhs: BoolOps) extends BoolOps
  case class BIn (lhs: BoolOps, rhs: BoolOps) extends BoolOps

  sealed trait Expr
  case class Resource(name: String, typ: String, attributes: Seq[Attribute]) extends Expr
  case class LeftEdge(parent: ARes, child: ARes) extends Expr
  case class RightEdge(parent: ARes, child: ARes) extends Expr
  case class Define(name: String, args: Seq[Argument], body: Seq[Expr]) extends Expr
  case class ITE(pred: BoolOps, thn: Seq[Expr], els: Option[Seq[Expr]]) extends Expr
}
