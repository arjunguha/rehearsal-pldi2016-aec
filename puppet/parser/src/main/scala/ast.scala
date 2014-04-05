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
case object And extends BoolBinOp
case object Or  extends BoolBinOp

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
// This is like values? Verify
sealed abstract class Leaf extends AST


// TODO : Refine, semantics are not clear yet
case class ASTBool (val value: Boolean) extends Leaf
case class ASTSTring (val value: String) extends Leaf
case class FlatString (val value: String) extends Leaf // Uninterpreted String
case class Concat extends Leaf
case class Default extends Leaf // Default class for case statement
case class Type extends Leaf 
case class Name extends Leaf
case class ClassName extends Leaf // Double colon separated class names
case class Undef extends Leaf
case class Hostname extends Leaf
case class Variable extends Leaf
case class HashOrArrayAccess extends Leaf
case class Regex extends Leaf


// Semantics : When this evaluates, the value of last expression pushed is returned which is head of the children list
case class BlockExpr (val exprs: List[Branch]) extends Branch

// Expressions involving operators
case class ArithExpr    (val lval: Branch, val rval: Branch, val op: ArithOp)    extends Branch
case class BoolBinExpr  (val lval: Branch, val rval: Branch, val op: BoolBinOp)  extends Branch
case class CompareExpr  (val lval: Branch, val rval: Branch, val op: CompareOp)  extends Branch
case class MatchExpr    (val lval: Branch, val rval: Branch, val op: MatchOp)    extends Branch
case class RelationExpr (val lval: Branch, val rval: Branch, val op: RelationOp) extends Branch
case class InExpr       (val lval: Branch, val rval: Branch) extends Branch
case class NotExpr      (val oper: Branch) extends Branch
case class Minus        (val oper: Branch) extends Branch


// Variable definition
case class Vardef (val name: Leaf, val value: Branch, val op: AssignOp) extends Branch

// Few Datastructures used by Puppet
case class ASTArray (private val arr: Array[Branch]) extends Branch
case class ASTHash (val kvs: List[(Leaf, Branch)]) extends Leaf

// Puppet Resource Decl Related nodes
case class ResourceParam (val param: Leaf, val value: Branch, val add: Option[Boolean]) extends Branch
case class ResourceInstance (val title: Leaf, val params: List[ResourceParam]) extends Branch
case class Resource (val typ: ClassName, val instances: List[ResourceInstance]) extends Branch
case class ResourceDefaults (val typ: Type, val params: List[ResourceParam]) extends Branch
case class ResourceReference (val typ: Leaf, val title: List[Branch]) extends Branch
case class ResourceOverride (val obj: ResourceReference, val params: List[ResourceParam]) extends Branch 

// Conditional Statements
case class If (val test: Branch, val true_exprs: BlockExpr, val false_exprs: BlockExpr) extends Branch
case class CaseOpt (val value: List[Leaf], val exprs: BlockExpr) extends Branch
case class CaseExpr (val test: Branch, val caseopts: List[CaseOpt]) extends Branch
case class Selector (val param: Leaf, val values: List[ResourceParam]) extends Branch

case class Collection (val typ: Type, val collectrhand: Branch, val params: List[ResourceParam]) extends Branch

case class Node (val hostnames: List[Leaf], val parent: Leaf, exprs: BlockExpr) extends TopLevelConstruct

case class Hostclass (val classname: String, val args: List[Branch], val parent: Option[Leaf], stmts: List[Branch]) extends Branch

case class Definition (val classname: String, val args: List[Branch], val exprs: BlockExpr) extends Branch

case class Functions (val name: String, val args: List[Branch]) extends Branch
