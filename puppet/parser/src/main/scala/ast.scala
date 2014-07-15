package puppet.syntax

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

/** These can appear in the body of a class */
sealed trait ClassBody extends StmtOrDecl

sealed trait TopLevelConstruct extends StmtOrDecl
sealed trait Statement extends StmtOrDecl with TopLevelConstruct
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

case class TopLevel(items: List[TopLevelConstruct]) extends AST

case class ASTBool (value: Boolean) extends RValue with SelectLHS with AttributeNameType

/** <b>Examples:</b>
 *
 * {@code 'hello'}, {@code 'hello${2 + 3}'}
 */
case class ASTString (value: String) extends RValue
                                     with HashKey
                                     with ResourceName
                                     with SelectLHS
                                     with AttributeNameType
                                     with Hostname

case object Default extends SelectLHS with Hostname

case class Type (value: String) extends RValue
                                with ResourceName
                                with ResourceRefType
                                with SelectLHS

case class Name (value: String)  extends RValue
                                 with HashKey
                                 with ResourceName
                                 with ResourceRefType
                                 with SelectLHS
                                 with AttributeNameType
                                 with Hostname

case object Undef extends RValue with SelectLHS

case class Variable (value: String) extends RValue
                                    with VardefLHS
                                    with ResourceName
                                    with SelectLHS
                                    with RelationExprOperand

case class HashOrArrayAccess (variable: Variable,
                              key: List[Expr]) extends RValue
                                               with VardefLHS
                                               with ResourceName
                                               with SelectLHS
                                               with RelationExprOperand

case class ASTRegex (value: String) extends Expr with SelectLHS with Hostname

case class ASTHash (kvs: List[(HashKey, Expr)]) extends Expr
case class ASTArray (arr: List[Expr]) extends RValue with ResourceName

case class BlockStmtDecls (stmts_decls: List[StmtOrDecl]) extends AST

// Expressions involving operators
case class BinExpr    (lhs: Expr, rhs: Expr, op: BinOp) extends Expr
case class NotExpr    (oper: Expr) extends Expr
case class UMinusExpr (oper: Expr) extends Expr

/**
 * {@code File['foo'] ~> File['bar']}, etc.
 */
case class RelationExpr (lhs: RelationExprOperand,
                         rhs: RelationExprOperand,
                          op: RelationOp) extends RelationExprOperand
                                          with Statement

case class Vardef (variable: VardefLHS,
                   value: Expr,
                   append: Boolean) extends Statement

/**
 * <b>Examples</b>
 *
 * {@code name => value} has {@code is_append} set to {@code false}.
 *
 * {@code name +> value} has {@code is_append} set to {@code true}.
 */
case class Attribute (name: AttributeNameType, value: Expr, is_append: Boolean)
  extends AST

// Puppet Resource Decl Related nodes
case class ResourceInstance (name: ResourceName, params: List[Attribute]) extends AST

case class Resource (name: String,
                     instances: List[ResourceInstance]) extends RelationExprOperand
                                                        with Statement

/**
 * <b>Examples</b>
 *
 * {@code File{ owner => nimish }}
 */
case class ResourceDefaults (typ: Type, params: List[Attribute])
  extends Statement

/**
 * <b>Examples</b>
 *
 * {@code File['/root/foo']}, {@code Package['vim']}
 */
case class ResourceRef (typ: ResourceRefType,
                        names: List[Expr]) extends RValue with RelationExprOperand
case class ResourceOverride (ref: ResourceRef,
                             params: List[Attribute]) extends Statement

case class VirtualResource (res: Resource,
                            tvirt: VirtualResType) extends Statement

case class CollectionExpr (lhs: CollectionExprOperand,
                           rhs: CollectionExprOperand,
                            op: CollectionOp) extends CollectionExprOperand

case class Collection (typ: Type,
                       collexpr: Option[CollectionExpr],
                       tvirt: VirtualResType,
                       params: List[Attribute]) extends RelationExprOperand
                                                with Statement

// Conditional Statements
case class IfStmt (test: Expr,
                   true_exprs: List[Statement],
                   false_exprs: List[Statement]) extends Statement

case class CaseOpt (values: List[SelectLHS], exprs: List[Statement]) extends AST

case class CaseExpr (test: Expr, caseopts: List[CaseOpt]) extends RelationExprOperand
                                                          with Statement

case class Selector (param: SelectLHS,
                     values: List[Attribute]) extends RValue
                                              with ResourceName
                                              with RelationExprOperand

case class Node (hostnames: List[Hostname],
                 parent: Option[Hostname],
                 stmts: List[Statement])
  extends TopLevelConstruct

// TODO : Should classname be string? or a 'Name' node or a 'Type' node?
case class Hostclass (classname: String,
                      args: List[(Variable, Option[Expr])],
                      parent: Option[String],
                      stmts: BlockStmtDecls)
  extends TopLevelConstruct with ClassBody


// TODO : Should classname be string? or a 'Name' node or a 'Type' node?
case class Definition (classname: String,
                       args: List[(Variable, Option[Expr])],
                       stmts: List[Statement])
  extends TopLevelConstruct with ClassBody

// This is a function application rather than function declaration
case class Function (name: Name,
                     args: List[Expr],
                     ftype: Functype) extends RValue
                                      with SelectLHS
                                      with Statement

case class Import (imports: List[String]) extends Statement
