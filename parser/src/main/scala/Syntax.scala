package parser

object Syntax {
  case class Attribute(name: String, value: Atom)

  sealed trait Atom
  case class ASymbol(name: String) extends Atom
  case class ABool(value: Boolean) extends Atom
  case class AString(value: String) extends Atom
  case class AVar(id: String) extends Atom

  sealed trait Expr
  case class Resource(name: String, typ: String, attributes: Seq[Attribute]) extends Expr
  case class LeftEdge(parent: String, child: String) extends Expr
  case class RightEdge(parent: String, child: String) extends Expr
}
