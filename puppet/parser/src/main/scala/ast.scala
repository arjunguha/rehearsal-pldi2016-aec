package puppet;

import scala.util.parsing.input.Positional

// Various Operators
sealed trait BinOp

case object Or          extends BinOp

case object And         extends BinOp

case object GreaterThan extends BinOp
case object GreaterEq   extends BinOp
case object LessThan    extends BinOp
case object LessEq      extends BinOp

case object NotEqual    extends BinOp
case object Equal       extends BinOp

case object LShift      extends BinOp
case object RShift      extends BinOp

case object Plus        extends BinOp
case object Minus       extends BinOp

case object Div         extends BinOp
case object Mult        extends BinOp
case object Mod         extends BinOp

case object Match       extends BinOp
case object NoMatch     extends BinOp
case object In          extends BinOp


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


// TODO : strict types (traits or heirarchy of types)



// AST

sealed trait AST extends Positional

case class ASTBool (val value: Boolean) extends AST
case class ASTString (val value: String) extends AST
// case class Concat (val lhs: AST, val rhs: AST)  extends AST
case object Default extends AST // Default class for case statement
case class Type (val value: String) extends AST 
case class Name (val value: String)  extends AST
case object Undef extends AST
case class Hostname (val value: String) extends AST
case class Variable (val value: String) extends AST
case class HashOrArrayAccess (val variable: AST, var key: AST) extends AST
case class ASTRegex (val value: String) extends AST
case class ASTHash (val kvs: List[(AST, AST)]) extends AST

// Semantics : When this evaluates, the value of last expression pushed is returned which is head of the children list
case class BlockExpr (val exprs: List[AST]) extends AST

// Expressions involving operators
case class BinExpr      (val lhs: AST, val rhs: AST, val op: BinOp)      extends AST
case class RelationExpr (val lhs: AST, val rhs: AST, val op: RelationOp) extends AST
case class NotExpr      (val oper: AST) extends AST
case class UMinusExpr   (val oper: AST) extends AST

// Variable definition
case class Vardef (val name: AST, val value: AST, val append: Boolean) extends AST

// Few Datastructures used by Puppet
case class ASTArray (val arr: List[AST]) extends AST

// Puppet Resource Decl Related nodes
// TODO : No val required for case classes
// TODO : pull out before and require from params in resource instances (separate desugaring)
case class ResourceParam (val param: AST, val value: AST, val add: Boolean) extends AST
case class ResourceInstance (val title: AST, val params: List[ResourceParam]) extends AST
case class Resource (val typ: String, val instances: List[ResourceInstance]) extends AST
case class ResourceDefaults (val typ: Type, val params: List[ResourceParam]) extends AST
case class ResourceRef (val typ: AST, val title: List[AST]) extends AST
case class ResourceOverride (val obj: ResourceRef, val params: List[ResourceParam]) extends AST 
case class VirtualResource (val res: AST, val tvirt: VirtualResType) extends AST

// Conditional Statements
case class IfExpr (val test: AST, val true_exprs: BlockExpr, val false_exprs: BlockExpr) extends AST
case class CaseOpt (val value: List[AST], val exprs: BlockExpr) extends AST
case class CaseExpr (val test: AST, val caseopts: List[CaseOpt]) extends AST
case class Selector (val param: AST, val values: List[ResourceParam]) extends AST

case class CollectionExpr (val lhs: AST, val rhs: AST, val op: CollectionOp) extends AST
case class CollectionExprTagNode (val coll: Option[CollectionExpr], val prop: VirtualResType) extends AST
case class Collection (val typ: Type, val collectrhand: AST, val params: List[ResourceParam]) extends AST

case class Node (val hostnames: List[Hostname], val parent: Option[String], exprs: BlockExpr) extends AST

case class Hostclass (val classname: String, val args: List[(String, Option[AST])], val parent: Option[String], stmts: BlockExpr) extends AST

case class Definition (val classname: String, val args: List[(String, Option[AST])], val exprs: BlockExpr) extends AST

case class Function (val name: String, val args: List[AST], val ftype: Functype) extends AST


case class Import (val imports: List[String]) extends AST
