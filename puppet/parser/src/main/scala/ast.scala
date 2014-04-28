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
case object Vrtvirtual  extends VirtualResType
case object Vrtexported extends VirtualResType


// TODO : strict types (traits or heirarchy of types)

// AST

sealed trait AST extends Positional

sealed trait Expr extends AST
trait RValue extends Expr

sealed trait HashKey extends AST
sealed trait VardefLHS extends AST

sealed trait ResourceName extends AST
sealed trait ResourceRefType extends AST

case class ASTBool (value: Boolean) extends AST with RValue
case class ASTString (value: String) extends AST with RValue with HashKey with ResourceName
case object Default extends AST // Default class for case statement
case class Type (value: String) extends AST  with RValue with ResourceName with ResourceRefType
case class Name (value: String)  extends AST with RValue with HashKey with ResourceName with ResourceRefType
case object Undef extends AST with RValue
case class Hostname (value: String) extends AST
case class Variable (value: String) extends AST with RValue with VardefLHS with ResourceName
case class HashOrArrayAccess (variable: Variable, 
                              key: List[Expr]) extends AST with RValue with VardefLHS with ResourceName
case class ASTRegex (value: String) extends AST with Expr
case class ASTHash (kvs: List[(HashKey, Expr)]) extends AST with Expr


case class ASTArray (arr: List[Expr]) extends AST with RValue with ResourceName

// Semantics : When this evaluates, the value of last expression pushed is returned which is head of the children list
// TODO : BlockExpr can go away
case class BlockExpr (exprs: List[AST]) extends AST

// Expressions involving operators
case class BinExpr      (lhs: Expr, rhs: Expr, op: BinOp) extends AST with Expr
case class NotExpr      (oper: Expr) extends AST with Expr
case class UMinusExpr   (oper: Expr) extends AST with Expr


case class RelationExpr (lhs: AST, rhs: AST, op: RelationOp) extends AST

// Variable definition
case class Vardef (variable: VardefLHS, value: Expr, append: Boolean) extends AST

// Few Datastructures used by Puppet

// Puppet Resource Decl Related nodes
// TODO : pull out before and require from params in resource instances (separate desugaring)
case class ResourceParam (param: AST, value: Expr, add: Boolean) extends AST
case class ResourceInstance (title: ResourceName, params: List[ResourceParam]) extends AST
case class Resource (typ: String, instances: List[ResourceInstance]) extends AST
case class ResourceDefaults (typ: Type, params: List[ResourceParam]) extends AST
case class ResourceRef (typ: ResourceRefType, title: List[Expr]) extends AST with RValue
case class ResourceOverride (obj: ResourceRef, params: List[ResourceParam]) extends AST 
case class VirtualResource (res: AST, tvirt: VirtualResType) extends AST

// Conditional Statements
case class IfExpr (test: AST, true_exprs: BlockExpr, false_exprs: BlockExpr) extends AST
case class CaseOpt (value: List[AST], exprs: BlockExpr) extends AST
case class CaseExpr (test: AST, caseopts: List[CaseOpt]) extends AST
case class Selector (param: AST, values: List[ResourceParam]) extends AST with RValue with ResourceName

case class CollectionExpr (lhs: AST, rhs: AST, op: CollectionOp) extends AST
case class CollectionExprTagNode (coll: Option[CollectionExpr], 
                                  prop: VirtualResType) extends AST
case class Collection (typ: Type,
                       collectrhand: CollectionExprTagNode, 
                       params: List[ResourceParam]) extends AST

case class Node (hostnames: List[Hostname],
                 parent: Option[String],
                 exprs: BlockExpr) extends AST

case class Hostclass (classname: String,
                      args: List[(Variable, Option[Expr])],
                      parent: Option[String],
                      stmts: BlockExpr) extends AST

case class Definition (classname: String,
                       args: List[(Variable, Option[Expr])],
                       exprs: BlockExpr) extends AST

case class Function (name: Name,
                     args: List[Expr],
                     ftype: Functype) extends AST

case class Import (imports: List[String]) extends AST
