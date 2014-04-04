import scala.util.parsing.input.Positional

sealed trait AST extends Positional

// TODO : Make mutable and appendable
sealed abstract class Branch (val children: List[Branch]) extends AST
sealed abstract class TopLevelConstruct extends AST
sealed abstract class Leaf[T] (val value: T) extends AST

// TODO : Make mutable and appendable
case class BlockExpr (val children: List[Branch]) extends Branch (children)
{
  def apply (i: int): Branch = children (i)

  // XXX : Wrong
  def push (b: Branch) = b :: children
}

case class Relationships (val lhs, val

