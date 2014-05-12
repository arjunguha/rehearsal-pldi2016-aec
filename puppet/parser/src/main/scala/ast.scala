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
sealed trait ResourceName extends AST with RValue
sealed trait ResourceRefType extends AST
sealed trait RelationExprOperand extends AST

sealed trait AttributeNameType extends AST
sealed trait SelectLHS extends AttributeNameType

sealed trait Hostname extends AST



case class ASTBool (value: Boolean) extends AST with RValue with SelectLHS with AttributeNameType
case class ASTString (value: String) extends AST 
                                     with RValue
                                     with HashKey
                                     with ResourceName
                                     with SelectLHS
                                     with RelationExprOperand
                                     with AttributeNameType
                                     with Hostname

case object Default extends AST with SelectLHS with Hostname
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
                                 with SelectLHS
                                 with AttributeNameType
                                 with Hostname

case object Undef extends AST with RValue with SelectLHS
case class Variable (value: String) extends AST
                                    with RValue
                                    with VardefLHS
                                    with ResourceName
                                    with SelectLHS
                                    with RelationExprOperand

case class HashOrArrayAccess (variable: Variable, 
                              key: List[Expr]) extends AST 
                                               with RValue
                                               with VardefLHS
                                               with ResourceName
                                               with SelectLHS
                                               with RelationExprOperand

case class ASTRegex (value: String) extends AST with Expr with SelectLHS with Hostname

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


case class Attribute (name: AttributeNameType, value: Expr, is_append: Boolean) extends AST


// Puppet Resource Decl Related nodes
case class ResourceInstance (title: ResourceName, params: List[Attribute]) extends AST
case class Resource (name: String, // TODO : String or AST String?
                     instances: List[ResourceInstance]) extends AST 
                                                        with RelationExprOperand
                                                        with Statement
case class ResourceDefaults (typ: Type, 
                             params: List[Attribute]) extends AST
                                                          with RelationExprOperand
                                                          with Statement

case class ResourceRef (typ: ResourceRefType,
                        titles: List[Expr]) extends AST with RValue with RelationExprOperand
case class ResourceOverride (ref: ResourceRef,
                             params: List[Attribute]) extends AST
                                                      with Statement

case class VirtualResource (res: Resource,
                            tvirt: VirtualResType) extends AST
                                                   with Statement

case class CollectionExpr (lhs: CollectionExprOperand,
                           rhs: CollectionExprOperand,
                            op: CollectionOp) extends AST with CollectionExprOperand

case class Collection (typ: Type,
                       collexpr: Option[CollectionExpr],
                       tvirt: VirtualResType,
                       params: List[Attribute]) extends AST 
                                                with RelationExprOperand
                                                with Statement

// Conditional Statements
case class IfExpr (test: Expr,
                   true_exprs: List[Statement],
                   false_exprs: List[Statement]) extends AST
                                            with Statement

case class CaseOpt (values: List[SelectLHS], exprs: List[Statement]) extends AST

case class CaseExpr (test: Expr, caseopts: List[CaseOpt]) extends AST
                                                          with RelationExprOperand
                                                          with Statement

case class Selector (param: SelectLHS,
                     values: List[Attribute]) extends AST
                                              with RValue
                                              with ResourceName
                                              with RelationExprOperand



case class Node (hostnames: List[Hostname],
                 parent: Option[Hostname],
                 stmts: List[Statement]) extends AST with TopLevelConstruct

// TODO : Should classname be string? or a 'Name' node or a 'Type' node?
case class Hostclass (classname: String,
                      args: List[(Variable, Option[Expr])],
                      parent: Option[String],
                      stmts: BlockStmtDecls) extends AST with TopLevelConstruct


// TODO : Should classname be string? or a 'Name' node or a 'Type' node?
case class Definition (classname: String,
                       args: List[(Variable, Option[Expr])],
                       stmts: List[Statement]) extends AST with TopLevelConstruct

// This is a function application rather than function declaration
//
case class Function (name: Name,
                     args: List[Expr],
                     ftype: Functype) extends AST 
                                      with RValue
                                      with SelectLHS
                                      with Statement

case class Import (imports: List[String]) extends AST with Statement
