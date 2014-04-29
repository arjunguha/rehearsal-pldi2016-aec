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


sealed trait AST extends Positional

sealed trait StmtOrDecl extends AST

sealed trait TopLevelConstruct extends StmtOrDecl
sealed trait Statement extends StmtOrDecl


sealed trait CollectionExprOperand extends AST
sealed trait Expr extends CollectionExprOperand
sealed trait RValue extends Expr

sealed trait HashKey extends AST
sealed trait VardefLHS extends AST
sealed trait ResourceName extends AST
sealed trait ResourceRefType extends AST
sealed trait RelationExprOperand extends AST

sealed trait ParamNameType extends AST
sealed trait SelectLHS extends ParamNameType



case class ASTBool (value: Boolean) extends AST with RValue with SelectLHS with ParamNameType
case class ASTString (value: String) extends AST 
                                     with RValue
                                     with HashKey
                                     with ResourceName
                                     with SelectLHS
                                     with RelationExprOperand
                                     with ParamNameType

case object Default extends AST with SelectLHS // Default class for case statement
case class Type (value: String) extends AST
                                with RValue
                                with ResourceName
                                with ResourceRefType
                                with SelectLHS

case class Name (value: String)  extends AST
                                 with RValue 
                                 with HashKey
                                 with ResourceName
                                 with ResourceRefType
                                 with CollectionExprOperand
                                 with SelectLHS
                                 with ParamNameType

case object Undef extends AST with RValue with SelectLHS
case class Hostname (value: String) extends AST
case class Variable (value: String) extends AST
                                    with RValue
                                    with VardefLHS
                                    with ResourceName
                                    with CollectionExprOperand
                                    with SelectLHS
                                    with RelationExprOperand

case class HashOrArrayAccess (variable: Variable, 
                              key: List[Expr]) extends AST 
                                               with RValue
                                               with VardefLHS
                                               with ResourceName
                                               with SelectLHS
                                               with RelationExprOperand

case class ASTRegex (value: String) extends AST with Expr with SelectLHS

case class ASTHash (kvs: List[(HashKey, Expr)]) extends AST with Expr
case class ASTArray (arr: List[Expr]) extends AST with RValue with ResourceName

case class BlockStmtDecls (stmts_decls: List[StmtOrDecl]) extends AST

// Expressions involving operators
case class BinExpr    (lhs: Expr, rhs: Expr, op: BinOp) extends AST with Expr
case class NotExpr    (oper: Expr) extends AST with Expr
case class UMinusExpr (oper: Expr) extends AST with Expr


case class RelationExpr (lhs: RelationExprOperand,
                         rhs: RelationExprOperand,
                          op: RelationOp) extends AST
                                          with RelationExprOperand
                                          with Statement

case class Vardef (variable: VardefLHS,
                   value: Expr, 
                   append: Boolean) extends AST with Statement 


// Puppet Resource Decl Related nodes
// TODO : pull out before and require from params in resource instances (separate desugaring)
case class ResourceParam (param: ParamNameType, value: Expr, add: Boolean) extends AST
case class ResourceInstance (title: ResourceName, params: List[ResourceParam]) extends AST
case class Resource (typ: String,
                     instances: List[ResourceInstance]) extends AST 
                                                        with RelationExprOperand
                                                        with Statement
case class ResourceDefaults (typ: Type, 
                             params: List[ResourceParam]) extends AST
                                                          with RelationExprOperand
                                                          with Statement

case class ResourceRef (typ: ResourceRefType,
                        title: List[Expr]) extends AST with RValue with RelationExprOperand
case class ResourceOverride (obj: ResourceRef,
                             params: List[ResourceParam]) extends AST
                                                          with Statement

case class VirtualResource (res: Resource,
                            tvirt: VirtualResType) extends AST
                                                   with Statement

// Conditional Statements
case class IfExpr (test: Expr,
                   true_exprs: List[Statement],
                   false_exprs: List[Statement]) extends AST
                                            with Statement

case class CaseOpt (value: List[SelectLHS], exprs: List[Statement]) extends AST

case class CaseExpr (test: Expr, caseopts: List[CaseOpt]) extends AST
                                                          with RelationExprOperand
                                                          with Statement

case class Selector (param: SelectLHS,
                     values: List[ResourceParam]) extends AST
                                                  with RValue
                                                  with ResourceName
                                                  with RelationExprOperand

case class CollectionExpr (lhs: CollectionExprOperand,
                           rhs: CollectionExprOperand,
                            op: CollectionOp) extends AST with CollectionExprOperand

case class CollectionExprTagNode (coll: Option[CollectionExpr], 
                                  prop: VirtualResType) extends AST
case class Collection (typ: Type,
                       collectrhand: CollectionExprTagNode, 
                       params: List[ResourceParam]) extends AST 
                                                    with RelationExprOperand
                                                    with Statement

case class Node (hostnames: List[Hostname],
                 parent: Option[String],
                 stmts: List[Statement]) extends AST with TopLevelConstruct

case class Hostclass (classname: String,
                      args: List[(Variable, Option[Expr])],
                      parent: Option[String],
                      stmts: BlockStmtDecls) extends AST with TopLevelConstruct

case class Definition (classname: String,
                       args: List[(Variable, Option[Expr])],
                       stmts: List[Statement]) extends AST with TopLevelConstruct

case class Function (name: Name,
                     args: List[Expr],
                     ftype: Functype) extends AST 
                                      with RValue
                                      with SelectLHS
                                      with Statement

case class Import (imports: List[String]) extends AST with Statement
