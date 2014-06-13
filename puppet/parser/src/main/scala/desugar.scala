package puppet.core

import puppet.syntax._

/* A 'Resource node' comprises of a type and numerous instances of that type.
 * It can be desugared from a list of resources grouped by their types into
 * individual resources with their types tagged onto them.
 *
 * Example of the above kind of desugaring
 *   file { 
 *     'pathA':
 *       ensure => present,
 *       content => 'Some Content',
 *     ;
 *     'pathB':
 *        ensure => present,
 *        content => 'Some other content'
 *   }
 *
 * Is equivalent to :=
 * file { 'pathA':
 *   ensure => present,
 *   content => 'Some Content'
 * }
 * file { 'pathB':
 *   ensure => present,
 *   content => 'Some Content'
 * }
 *
 * Of course, it may not be able to desugar the below representation into
 * its constituent resources as it can only be done upon evaluation of 
 * variable
 *
 * $arr = ['pathA', 'pathB']
 * file { $arr:
 *   ensure => present
 * }
 */

/*
 * One more difference from the Sugar Language AST is that some key attributes
 * of a resource now occur explicitly as attributes, like -
 * - type of resource
 * - title of resource
 * - virtual status of resource
 *
 * These are just attributes and I don't see any point why they should
  * receive special treatment at this time.
 *
 * Example:
 * 
 *  @file {'/tmp/file': ensure => present } is desugared into
 *
 *  ResourceDeclaration {
 *     type => 'File',
 *     title => '/tmp/file',
 *     virtual => true,
 *     ensure => present
 *  }
 */

/*
 * An important desugaring is that of ResourceReference and ResourceCollection
 * 
 * Semantically, they are same as they try to refer to one or more
 * resources. The former references a single resource by its type and
 * title and the latter is a generic search over attributes of a particular
 * type of resource. We can treat 'ResourceReference' as a special case of
 * 'Collection' as a search on the title (which happens to be unique for a
 * type of resource across catalog/system). Since we have title of a resource
 * as another attribute due to one of the above desugaring, it blends nicely
 * with our core AST semantics.
 */

/* RelationExpr
 * 
 * Multiple possible directions of dependence are desugared into a single direction
 *
 * in-attribute ('before', 'after', 'subscribe', 'notify') dependencies are handled
 * at the time of evaluation.
 */

/*
 * Another important desugaring aspect is ResourceDefaults, Collection and
 * ResourceOverriding. Semantically, these are equivalent. ResourceDefaults
 * and Collection overrides the default behaviour of resources of a particular
 * type and ResourceOverride construct overrides a particular instance of a type of
 * resource. Changing the default behaviour of resources applies the new property to
 * every instance of that resource and hence overriding a particular instance
 * is a special case which can be desugared similarly to the desugaring of 
 * resource references above. Due to that desugaring, we get a similar kind of 
 * behaviour for overriding as well. Example
 * 
 * File { checksum => md5lite  } # override overrall default file attributes
 * Service ['apache'] { ensure => stopped } # Overriding status for apache service
 * # Overriding path for all executables that are statically linked
 * Exec <| tag == 'staticlink' |> { path => '/sbin/:/usr/sbin' }
 *
 * is desugared into
 *
 * ResourceOverride (type == 'file') { checksum => md5lite }
 * ResourceOverride (type == 'service' and title == 'apache') { ensure => stopped }
 * ResourceOverride (type == 'exec' and tag == 'staticlink') { path => '/sbin/:/usr/sbin' }
 * 
 * respectively.
 */

/* Node construct that specifies multiple node declaration sharing common code
 * is desugared into array of Nodes.
 */

/*
 * Branching constructs like case, selector and if-else are desugared into if-else
 * constructs.
 */


sealed abstract trait FilterOp
case object FEqOp    extends FilterOp
case object FNotEqOp extends FilterOp
case object FAndOp   extends FilterOp
case object FOrOp    extends FilterOp

sealed abstract trait ASTCore

// TODO : Use scala type system for precise types
case object UndefC extends ASTCore  // Special value for unassigned variables
case class BoolC (value: Boolean) extends ASTCore 
case class StringC (value: String) extends ASTCore 
case class TypeC (value: String) extends ASTCore 
case class NameC (value: String) extends ASTCore 
case class RegexC (value: String) extends ASTCore 
case class ASTHashC (kvs: List[(ASTCore, ASTCore)]) extends ASTCore
case class ASTArrayC (arr: List[ASTCore]) extends ASTCore 
case class HashOrArrayAccessC (variable: VariableC, keys: List[ASTCore]) extends ASTCore 
case class VariableC (value: String) extends ASTCore 
case class BlockStmtC (exprs: List[ASTCore]) extends ASTCore
case class IfElseC (test: ASTCore, true_br: ASTCore, false_br: ASTCore) extends ASTCore
case class BinExprC (lhs: ASTCore, rhs: ASTCore, op: BinOp) extends ASTCore
case class NotExprC (oper: ASTCore) extends ASTCore
case class FuncAppC (name: ASTCore, args: List[ASTCore]) extends ASTCore 
case class ImportC (imports: List[String]) extends ASTCore
case class VardefC (variable: ASTCore, value : ASTCore , append: Boolean) extends ASTCore
case class OrderResourceC (source: ASTCore, target: ASTCore, refresh: Boolean) extends ASTCore
case class AttributeC (name: ASTCore, value: ASTCore, is_append: Boolean) extends ASTCore
case class ResourceDeclC (attrs: List[ASTCore]) extends ASTCore
// case class ResourceRefC (filter: ASTCore) extends ASTCore 
case class FilterExprC (lhs: ASTCore, rhs: ASTCore, op: FilterOp) extends ASTCore

case class ResourceOverrideC (ref : ASTCore, attrs : List[ASTCore]) extends ASTCore
case class NodeC (hostname: ASTCore, parent: Option[ASTCore], stmts: ASTCore /* BlockStmtC */) extends ASTCore

/* 
 * A class in puppet is a collection of (possibly distinct types) resources. The
 * parameters add flexibility to the resources in class
 */
case class HostclassC (classname: String, args: List[(VariableC, Option[ASTCore])], parent: Option[String], stmts: ASTCore /* BlockStmtC */) extends ASTCore

/* 
 * A 'define' is like a user-defined resource type and the parameters of a 'define'
 * are like attributes of that resource type
 */
case class DefinitionC (classname: String, args: List[(VariableC, Option[ASTCore])], stmts: ASTCore /* BlockStmtC */) extends ASTCore



object DesugarPuppetAST {

  private def flatMap (block: BlockStmtC): BlockStmtC = {
    BlockStmtC (block.exprs.map ({ case ast: ASTCore => ast match {
      case b : BlockStmtC => b.exprs
      case _ => List (ast)
    }}).flatten)
  }

  def desugarAST (ast: AST): ASTCore = ast match {

    case ASTBool (b) => BoolC (b)
    case ASTString (s) => StringC (s)
    case Default => throw new Exception ("Default should have been Unreachable")
    case Type (t) => TypeC (t)
    case Name (name) => NameC (name)
    case Undef => UndefC
    case Variable (v) => VariableC (v)
    case Vardef (v, value, append) => VardefC (desugarAST (v), desugarAST (value), append)
    case ASTRegex (r) => RegexC (r)
    case ASTHash (kvs) => ASTHashC (kvs.map { case (key, value) => 
                                                    (desugarAST (key), desugarAST (value)) })
    case ASTArray (arr) => ASTArrayC (arr.map (desugarAST (_)))
    case HashOrArrayAccess (v, ks) => HashOrArrayAccessC (VariableC (v.value), ks.map (desugarAST (_)))
    case BlockStmtDecls (stmts_decls) => flatMap (BlockStmtC ( stmts_decls.map { desugarAST (_) }))
    case BinExpr (lhs, rhs, op) => BinExprC (desugarAST (lhs), desugarAST (rhs), op)
    case NotExpr (oper) => NotExprC (desugarAST (oper))
    case UMinusExpr (oper) => BinExprC (NameC ("-1"), desugarAST (oper), Mult)

    case RelationExpr (lhs, rhs, op) => {
      val lhsd = desugarAST(lhs)
      val rhsd = desugarAST(rhs)

      op match {
        case LeftSimpleDep     => OrderResourceC (rhsd, lhsd, false)
        case RightSimpleDep    => OrderResourceC (lhsd, rhsd, false)
        case LeftSubscribeDep  => OrderResourceC (rhsd, lhsd, true)
        case RightSubscribeDep => OrderResourceC (lhsd, rhsd, true)
      }
    }
       
    case Attribute (name, value, add) => AttributeC (desugarAST (name), desugarAST (value), add)

    case ResourceInstance (title, params) => {
      val titleattr = Attribute (Name ("title"), title, false /* no add */)
      ResourceDeclC ((titleattr :: params).map (desugarAST (_)))
    }

    case Resource (typ, instances) => {

      // Desugar into a ResourceC while adding 'type' as another attribute
      val typeattr = Attribute (Name("type"), Type (typ.capitalize), false /*no add*/)
      val insts_with_tattr = instances.map ((r) => ResourceInstance (r.title, typeattr :: r.params))

      BlockStmtC (insts_with_tattr.map (desugarAST (_)))
    }

    case VirtualResource (res, tvirt) => {
      // Add virtual as an attribute to resource
      val instances = res.instances

      val virtattr = tvirt match {
        case Vrtvirtual  => Attribute (Name ("virtual"), ASTString ("virtual"), false /* no add */)
        case Vrtexported => Attribute (Name ("virtual"), ASTString ("exported"), false /* no add */)
      }

      val insts_with_vattr = instances.map ((r) => ResourceInstance (r.title, virtattr :: r.params))
      desugarAST (Resource (res.name, insts_with_vattr))
    }

 
    case ResourceRef (typ, titles) => {
      // A resource should have the attributes
      val restyp = typ match {
        // Name is effectively a type, see the corresponding production rule
        case Name (name) => Type (name.capitalize)
        case typ => typ
      }

      val typmatch = FilterExprC (NameC ("type"), desugarAST (restyp), FEqOp)
      val filters = titles.map ((title) => (FilterExprC (FilterExprC (NameC ("title"), desugarAST (title), FEqOp),
                                                         typmatch, FAndOp)))
      val filter = filters.reduce(FilterExprC (_, _, FOrOp))
      filter
    }

    case CollectionExpr (lhs, rhs, op) => op match {
      case CollOr    => FilterExprC(desugarAST(lhs), desugarAST(rhs), FOrOp)
      case CollAnd   => FilterExprC(desugarAST(lhs), desugarAST(rhs), FAndOp)
      case CollIsEq  => FilterExprC(desugarAST(lhs), desugarAST(rhs), FEqOp)
      case CollNotEq => FilterExprC(desugarAST(lhs), desugarAST(rhs), FNotEqOp)
    }

    case Collection (typ, collexpr, tvirt, params) => {
     /*
      * Behaviour: 
      *   - When used in chaining, virtual tag is ignored
      *   - When used as overriding construct, virtual tag is ignored
      *   - When used as a value they realize virtual resources (virtual tag kicks in)
      */

      if (params.length == 0) {
        // Either chaining or realizing virtual resource, lets preserve the virtual tag
        val typmatchexpr = CollectionExpr (Name ("type"), typ, CollIsEq)
        val virtmatchexpr = tvirt match {
          case Vrtvirtual => CollectionExpr (Name ("virtual"), ASTString ("virtual"), CollIsEq)
          case Vrtexported => CollectionExpr (Name ("virtual"), ASTString ("exported"), CollIsEq)
        }

        val filter = desugarAST (collexpr match {
          case Some (collexpr) => CollectionExpr(collexpr,
                                                 CollectionExpr (virtmatchexpr, typmatchexpr, CollAnd),
                                                 CollAnd)
          case None => CollectionExpr(virtmatchexpr, typmatchexpr, CollAnd)
        })

        filter
      }
      else {
        // Overriding, virtual tag should be ignored
        val typmatchexpr = CollectionExpr (Name ("type"), typ, CollIsEq)
        val filter = desugarAST (collexpr match {
          case Some (collexpr) => CollectionExpr (collexpr, typmatchexpr, CollAnd)
          case None => typmatchexpr
        })

        ResourceOverrideC (filter, params.map (desugarAST (_)))
      }
    }

    case ResourceOverride (ref, params) => ResourceOverrideC (desugarAST (ref), params.map (desugarAST (_)))
    case ResourceDefaults (typ, params) => {
      val filter = FilterExprC (NameC ("type"), TypeC (typ.value.capitalize), FEqOp)
      ResourceOverrideC (filter, params.map (desugarAST (_)))
    }

    case IfExpr (test, true_exprs, false_exprs) =>
      IfElseC (desugarAST (test), BlockStmtC (true_exprs.map (desugarAST (_))), BlockStmtC (false_exprs.map (desugarAST (_))))

    case CaseOpt (values, exprs) => throw new Exception ("CaseOpt should have been Unreachable")

    case CaseExpr (test, caseopts) => {

      // extract 'default' case expression
      def is_default (co: CaseOpt) = co.values match {
        case Default :: Nil => true
        case _ => false
      }

      /* Order of tests is important and needs to be preserved except for 'default'
       */
      val p = caseopts.partition (is_default)

      val default_caseopt  = p._1
      val regular_caseopts = p._2

      val testC = desugarAST (test)

      val defaultBlockC: ASTCore = BlockStmtC (
        if (default_caseopt.length != 0) default_caseopt.head.exprs.map (desugarAST (_))
        else List ())

      // Desugar "regular" case options to if-else constructs
      regular_caseopts.foldRight (defaultBlockC) { (elem, acc) => 
        val iftestC = elem.values.foldRight (BoolC (false): ASTCore) ((elem, acc) => 
          BinExprC (BinExprC (desugarAST (elem), testC, Equal), acc, Or))
        IfElseC (iftestC, BlockStmtC (elem.exprs.map (desugarAST (_))), acc)
      }
    }

    // Selector return values (that can possibly be assigned to variables) while case statement evaluation do not return any valuE
    case Selector (test, attrs) => {

      // extract 'default' case expression
      def is_default (attr: Attribute) = attr.name match {
        case Default  => true
        case _ => false
      }

      /* Order of tests is important and needs to be preserved except for 'default'
       */
      val p = attrs.partition (is_default)

      val default_attr  = p._1
      val regular_attrs = p._2
      
      val defaultBlockC: ASTCore = BlockStmtC (
        if (default_attr.length != 0) List (desugarAST (default_attr.head.value))
        else List ())

      // Desugar "regular" case options to if-else constructs
      regular_attrs.foldRight (defaultBlockC) { (attr, block) => 
        val iftestC = BinExprC (desugarAST (attr.name), desugarAST (test), Equal)
        IfElseC (iftestC, BlockStmtC (List (desugarAST (attr.value))), block)
      }
    }

    case Node (hostnames, None, stmts) => {
      val desugared_stmts = desugarAST (BlockStmtDecls (stmts))
      BlockStmtC (hostnames.map (desugarAST (_)).map (NodeC (_, None, desugared_stmts)))
    }

    case Node (hostnames, Some (parent), stmts) => {
      val desugared_stmts = desugarAST (BlockStmtDecls (stmts))
      BlockStmtC (hostnames.map (desugarAST (_)).map (NodeC (_, Some (desugarAST (parent)), desugared_stmts)))
    }

    case Hostclass (classname, args, parent, stmts) => 
      HostclassC (classname,
                  args.map { case (v, None)     => (VariableC (v.value), None)
                             case (v, Some (e)) => (VariableC (v.value), Some (desugarAST (e))) },
                  parent,
                  desugarAST (stmts))

    case Definition (classname, args, stmts) => 
      DefinitionC (classname, args.map ({ case (v, None) => (VariableC (v.value), None)
                                          case (v, Some (e)) => (VariableC (v.value), Some (desugarAST (e))) }),
                   desugarAST (BlockStmtDecls (stmts)))

    case Function (name, args, _) => FuncAppC (desugarAST (name), args.map (desugarAST (_)))
    case Import (imports) => ImportC (imports)
  }

  // TODO : apply method
}
