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
case object NotEqual    extends CompareOp
case object Equal       extends CompareOp
case object GreaterThan extends CompareOp
case object GreaterEq   extends CompareOp
case object LessThan    extends CompareOp
case object LessEq  extends CompareOp


sealed trait MatchOp
case object Match   extends MatchOp
case object NoMatch extends MatchOp


sealed trait RelationOp
case object LeftSimpleDep     extends RelationOp
case object RightSimpleDep    extends RelationOp
case object LeftSubscribeDep  extends RelationOp
case object RightSubscribeDep extends RelationOp


sealed trait CollectionOp
case object CollOr    extends CollectionOp
case object CollAnd   extends CollectionOp
case object CollIsEq  extends CollectionOp
case object CollNotEq extends CollectionOp


sealed trait Functype
case object Ftstmt extends Functype
case object Ftrval  extends Functype


sealed trait VirtualResType
case object Vrtvirtual extends VirtualResType
case object Vrtexported extends VirtualResType



// AST

sealed trait AST extends Positional

sealed abstract class Branch extends AST
sealed abstract class TopLevelConstruct extends AST
sealed abstract class Leaf extends AST

case class ASTBool (val value: Boolean) extends Leaf
case class ASTString (val value: String) extends Leaf
case class Concat (val lhs: AST, val rhs: AST)  extends Leaf
case class Default extends Leaf // Default class for case statement
case class Type (val value: String) extends Leaf 
case class Name (val value: String)  extends Leaf
case object Undef extends Leaf
case class Hostname (val value: String) extends Leaf
case class Variable (val value: String) extends Leaf
case class HashOrArrayAccess (val variable: Leaf, var key: AST) extends Leaf
case class ASTRegex (val value: String) extends Leaf
case class ASTHash (val kvs: List[(String, AST)]) extends Leaf

// Semantics : When this evaluates, the value of last expression pushed is returned which is head of the children list
case class BlockExpr (val exprs: List[AST]) extends Branch

// Expressions involving operators
case class ArithExpr    (val lval: AST, val rval: AST, val op: ArithOp)    extends Branch
case class BoolBinExpr  (val lval: AST, val rval: AST, val op: BoolBinOp)  extends Branch
case class CompareExpr  (val lval: AST, val rval: AST, val op: CompareOp)  extends Branch
case class InExpr       (val lval: AST, val rval: AST) extends Branch
case class RelationExpr (val lval: AST, val rval: AST, val op: RelationOp) extends Branch
case class MatchExpr    (val lval: AST, val rval: ASTRegex, val op: MatchOp)    extends Branch
case class NotExpr      (val oper: AST) extends Branch
case class UMinusExpr   (val oper: AST) extends Branch


// Variable definition
case class Vardef (val name: Leaf, val value: AST, val append: Boolean) extends Branch

// Few Datastructures used by Puppet
case class ASTArray (private val arr: List[AST]) extends Branch

// Puppet Resource Decl Related nodes
case class ResourceParam (val param: AST, val value: AST, val add: Boolean) extends Branch
case class ResourceInstance (val title: AST, val params: List[ResourceParam]) extends Branch
case class Resource (val typ: String, val instances: List[ResourceInstance]) extends Branch
case class ResourceDefaults (val typ: Type, val params: List[ResourceParam]) extends Branch
case class ResourceRef (val typ: Leaf, val title: List[AST]) extends Branch
case class ResourceOverride (val obj: ResourceRef, val params: List[ResourceParam]) extends Branch 
case class VirtualResource (val res: Branch, val tvirt: VirtualResType) extends Branch

// Conditional Statements
case class IfExpr (val test: AST, val true_exprs: BlockExpr, val false_exprs: BlockExpr) extends Branch
case class CaseOpt (val value: List[AST], val exprs: BlockExpr) extends Branch
case class CaseExpr (val test: AST, val caseopts: List[CaseOpt]) extends Branch
case class Selector (val param: AST, val values: List[ResourceParam]) extends Branch

case class CollectionExpr (val lhs: AST, val rhs: AST, val op: CollectionOp) extends Branch
case class CollectionExprTagNode (val coll: Option[CollectionExpr], val prop: VirtualResType) extends Branch
case class Collection (val typ: Type, val collectrhand: Branch, val params: List[ResourceParam]) extends Branch

case class Node (val hostnames: List[Hostname], val parent: Option[String], exprs: BlockExpr) extends TopLevelConstruct

case class Hostclass (val classname: String, val args: List[(String, Option[AST])], val parent: Option[String], stmts: BlockExpr) extends Branch

case class Definition (val classname: String, val args: List[(String, Option[AST])], val exprs: BlockExpr) extends TopLevelConstruct

case class Function (val name: String, val args: List[AST], val ftype: Functype) extends Branch


case class Import (val imports: List[String]) extends Branch
