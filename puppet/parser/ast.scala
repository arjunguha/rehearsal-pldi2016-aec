import scala.util.parsing.input.Positional


// Various Operators


sealed trait ArithOp
case object Plus   extends ArithOp
case object Minus  extends ArithOp
case object Div    extends ArithOp
case object Mult   extends ArithOp
case object Mod    extends ArithOp
case object LShift extends ArithOp
case object RShift extends ArithOp


sealed trait BoolBinOp
case object And extends BoolOp
case object Or  extends BoolOp

sealed trait CompareOp
case object Equal    extends CompareOp
case object NotEqual extends CompareOp

sealed trait MatchOp
case object Match   extends MatchOp
case object NoMatch extends MatchOp


sealed trait RelationOp
case object LeftSimpleDep extends RelationOp
case object RightSimleDep extends RelationOp
case object LeftSubsDep   extends RelationOp
case object RightSubsDep  extends RelationOp

sealed trait AssignOp
case object SimplAssign  extends AssignOp
case object AppendAssing extends AssignOp

// AST

sealed trait AST extends Positional

// Branch is like main Expr? Verify
sealed abstract class Branch extends AST
sealed abstract class TopLevelConstruct extends AST
sealed abstract class Leaf extends AST
sealed abstract class TopLevelConstruct extends AST

// Semantics : When this evaluates, the value of last expression pushed is returned which is head of the children list
case class BlockExpr (val exprs: List[Branch]) extends Branch

// Expressions involving operators
case class ArithExpr (val lval: Branch, val rval: Branch, val op: ArithOp) extends Branch
case class BoolBinExpr (val lval: Branch, val rval: Branch, val op: BoolBinOp) extends Branch
case class NotExpr (val oper: Branch) extends Branch
case class CompareExpr (val lval: Branch, val rval: Branch, val op: CompareOp) extends Branch
case class InExpr (val lval: Branch, val rval: Branch) extends Branch
case class MatchExpr (val lval: Branch, val rval: Branch, val op: MatchOp) extends Branch
case class Minus (val value: Branch) extends Branch
case class RelationExpr (val lval: Branch, val rval: Branch, val op: RelationOp) extends Branch


// Variable definition
case class Vardef (val name: Leaf, val value: Branch, val op: AssignOp) extends Branch


// Conditional Statements
case class If (val test: Branch, val true_exprs: BlockExpr, val false_exprs: BlockExpr) extends Branch
case class CaseOpt (val value: List[/* Some type, I believe (mostly) Leaf but I am not sure */], val exprs: BlockExpr) extends Branch
case class CaseExpr (val test: Branch, val caseopts: List[CaseOpt]) extends Branch
case class Selector (val control_val: /* some type, I believe (mostly) Leaf but I am not sure */, val exprs: List[/* selectval */]) extends Branch

case class Collection (val type: Leaf /* TODO: More Specific */, val collectrhand: Branch, val params: List[ResourceParam]) extends Branch

case class Node (val hostnames: List[Leaf], val parent: Leaf, exprs: BlockExpr) extends TopLevelConstruct


case class Define (val classname: Leaf /* TODO: More specific */, val args: List[Branch], val exprs: BlockExpr) extends Branch


case class Class (val name: String, val class_args: List[

case class Functions (val name: String, val args: List[Branch]) extends Branch


case class ASTArray (private val arr: Array[Branch]) extends Branch
case class ASTHash (val kvs: List[(Leaf, Branch)]) extends Leaf
