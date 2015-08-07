package parser

import parser.{Internal => I}

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
  case class BAtom(atom: Atom) extends BoolOps
  case class BAnd(lhs: BoolOps, rhs: BoolOps) extends BoolOps
  case class BOr(lhs: BoolOps, rhs: BoolOps) extends BoolOps
  case class BNot(arg: BoolOps) extends BoolOps
  case class BEq(lhs: BoolOps, rhs: BoolOps) extends BoolOps
  case class BNEq(lhs: BoolOps, rhs: BoolOps) extends BoolOps
  case class BMatch(lhs: BoolOps, rhs: BoolOps) extends BoolOps
  case class BNMatch(lhs: BoolOps, rhs: BoolOps) extends BoolOps
  case class BIn(lhs: BoolOps, rhs: BoolOps) extends BoolOps

  sealed trait Expr
  case class Resource(name: String, typ: String, attributes: Seq[Attribute]) extends Expr
  case class LeftEdge(parent: ARes, child: ARes) extends Expr
  case class RightEdge(parent: ARes, child: ARes) extends Expr
  case class Define(name: String, args: Seq[Argument], body: Seq[Expr]) extends Expr
  case class ITE(pred: BoolOps, thn: Seq[Expr], els: Option[Seq[Expr]]) extends Expr

  def convertAtom(atom: Atom): I.Atom = atom match {
    case ASymbol(name) => I.ASymbol(name)
    case ABool(value) => I.ABool(value)
    case AString(value) => I.AString(value)
    case AVar(id) => I.AVar(id)
    case ARes(typ, id) => I.ARes(typ, id)
  }

  def convertBoolOps(bop: BoolOps): I.BoolOps = bop match {
    case BAtom(atom) => I.BAtom(convertAtom(atom))
    case BAnd(lhs, rhs) => (convertBoolOps(lhs), convertBoolOps(rhs)) match {
      case (ilhs, irhs) => I.BNAnd(I.BNAnd(ilhs, irhs), I.BNAnd(ilhs, irhs))
    }
    case BOr(lhs, rhs) => (convertBoolOps(lhs), convertBoolOps(rhs)) match {
      case (ilhs, irhs) => I.BNAnd(I.BNAnd(ilhs, ilhs), I.BNAnd(irhs, irhs))
    }
    case BNot(arg) => convertBoolOps(arg) match {
      case iarg => I.BNAnd(iarg, iarg)
    }
    case BEq(lhs, rhs) => I.BEq(convertBoolOps(lhs), convertBoolOps(rhs))
    case BNEq(lhs, rhs) => I.BNEq(convertBoolOps(lhs), convertBoolOps(rhs))
    case BMatch(lhs, rhs) => I.BMatch(convertBoolOps(lhs), convertBoolOps(rhs))
    case BNMatch(lhs, rhs) => I.BNMatch(convertBoolOps(lhs), convertBoolOps(rhs))
    case BIn(lhs, rhs) => I.BIn(convertBoolOps(lhs), convertBoolOps(rhs))
  }

  def convertAttribute(attr: Attribute): I.Attribute = attr match {
    case Attribute(name, value) => I.Attribute(name, convertAtom(value))
  }

  def convertAttributes(attrs: Seq[Attribute]): Seq[I.Attribute] = attrs.map(convertAttribute)

  def convertArgument(arg: Argument): I.Argument = arg match {
    case Argument(id, typ, default) => I.Argument(id, typ, default.map(convertAtom))
  }

  def convertArguments(args: Seq[Argument]): Seq[I.Argument] = args.map(convertArgument)

  def convert(expr: Expr): I.Expr = expr match {
    case Resource(name, typ, attributes) => I.Resource(name, typ, convertAttributes(attributes))
    case LeftEdge(ARes(ptyp, pid), ARes(ctyp, cid)) => I.Edge(I.ARes(ptyp, pid), I.ARes(ctyp, cid))
    case RightEdge(ARes(ptyp, pid), ARes(ctyp, cid)) => I.Edge(I.ARes(ptyp, pid), I.ARes(ctyp, cid))
    case Define(name, args, body) => I.Define(name, convertArguments(args), convertAll(body))
    case ITE(pred, thn, els) => I.ITE(convertBoolOps(pred), convertAll(thn), els.map(convertAll))
  }

  def convertAll(exprs: Seq[Expr]): Seq[I.Expr] = exprs.map(convert)
}
