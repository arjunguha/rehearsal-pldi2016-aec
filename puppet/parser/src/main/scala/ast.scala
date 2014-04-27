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
case object Ftrval extends Functype


sealed trait VirtualResType
case object Vrtvirtual extends VirtualResType
case object Vrtexported extends VirtualResType


// TODO : strict types (traits or heirarchy of types)



// AST

sealed trait AST extends Positional

case class ASTBool (value: Boolean) extends AST
case class ASTString (value: String) extends AST
case object Default extends AST // Default class for case statement
case class Type (value: String) extends AST 
case class Name (value: String)  extends AST
case object Undef extends AST
case class Hostname (value: String) extends AST
case class Variable (value: String) extends AST
case class HashOrArrayAccess (variable: AST, var key: AST) extends AST
case class ASTRegex (value: String) extends AST
case class ASTHash (kvs: List[(AST, AST)]) extends AST

// Semantics : When this evaluates, the value of last expression pushed is returned which is head of the children list
case class BlockExpr (exprs: List[AST]) extends AST

// Expressions involving operators
case class BinExpr      (lhs: AST, rhs: AST, op: BinOp)      extends AST
case class RelationExpr (lhs: AST, rhs: AST, op: RelationOp) extends AST
case class NotExpr      (oper: AST) extends AST
case class UMinusExpr   (oper: AST) extends AST

// Variable definition
case class Vardef (name: AST, value: AST, append: Boolean) extends AST

// Few Datastructures used by Puppet
case class ASTArray (arr: List[AST]) extends AST

// Puppet Resource Decl Related nodes
// TODO : No required for case classes
// TODO : pull out before and require from params in resource instances (separate desugaring)
case class ResourceParam (param: AST, value: AST, add: Boolean) extends AST
case class ResourceInstance (title: AST, params: List[ResourceParam]) extends AST
case class Resource (typ: String, instances: List[ResourceInstance]) extends AST
case class ResourceDefaults (typ: Type, params: List[ResourceParam]) extends AST
case class ResourceRef (typ: AST, title: List[AST]) extends AST
case class ResourceOverride (obj: ResourceRef, params: List[ResourceParam]) extends AST 
case class VirtualResource (res: AST, tvirt: VirtualResType) extends AST

// Conditional Statements
case class IfExpr (test: AST, true_exprs: BlockExpr, false_exprs: BlockExpr) extends AST
case class CaseOpt (value: List[AST], exprs: BlockExpr) extends AST
case class CaseExpr (test: AST, caseopts: List[CaseOpt]) extends AST
case class Selector (param: AST, values: List[ResourceParam]) extends AST

case class CollectionExpr (lhs: AST, rhs: AST, op: CollectionOp) extends AST
case class CollectionExprTagNode (coll: Option[CollectionExpr], prop: VirtualResType) extends AST
case class Collection (typ: Type, collectrhand: AST, params: List[ResourceParam]) extends AST

case class Node (hostnames: List[Hostname], parent: Option[String], exprs: BlockExpr) extends AST

case class Hostclass (classname: String, args: List[(String, Option[AST])], parent: Option[String], stmts: BlockExpr) extends AST

case class Definition (classname: String, args: List[(String, Option[AST])], exprs: BlockExpr) extends AST

case class Function (name: String, args: List[AST], ftype: Functype) extends AST


case class Import (imports: List[String]) extends AST
