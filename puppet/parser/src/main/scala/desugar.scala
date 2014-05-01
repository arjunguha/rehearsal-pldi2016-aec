package puppet

/* How to go about desugaring
 *  - Resource Ordering/Dependencies should be clearly visible
 *  - Some operators are superfluous
 *  - IfExprs, Case options and Selectors into a common node
 *  - "node" concept is only applicable when we get into master and client mode
 *  - Functions
 *  - Imports
 *  - Declarations: Node vs Hostclass vs Definition
 */


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
 *     type => File,
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
 * title and the latter is a generic search over a particular type of 
 * resource involving some property (match or no match) on its attributes.
 * We can treat 'ResourceReference' as a special case of 'Collection' as a
 * search on the title (which happens to be unique for a type of resource 
 * across catalog/system). Since we have title of a resource as another
 * attribute due to one of the above desugaring, it blends nicely with our
 * core AST semantics. 
 */


/* RelationExpr is desugared into a ordering relation of two resources.
 *
 * A difference from sugared AST semantics is that the sugared AST accepts
 * either a resource, or a resource reference, effectively mixing resource
 * declaration and ordering. Here, we keep the declaration of resource 
 * separate from ordering to keep types simple. This will simplify
 * its evaluation as well. An example is discussed below :-
 *
 * file { '/tmp/dir/': ensure => directory } 
 *   -> file { '/tmp/dir/file1': ensure => file }
 * is desugared into
 * 
 * file {'/tmp/dir': ensure => directory }
 * file {'/tmp/dir/file': ensure => file }
 * File ['/tmp/dir'] -> Fiel ['/tmp/dir/file']
 *
 * Multiple possible directions of dependence are desugared into a single direction
 *
 * The original AST node could order a list of resources (groups of resources)
 * but to keep things simple here, we order only two (groups of) resources. It
 * specifies the order among any two (groups of) resources. This should keep the
 * types simple (at expense of some redundancy in core AST) without having an
 * impact on evaluation.
 *
 * Example: 
 *
 * File ['/tmp/dir1'] -> File['/tmp/dir1/dir2'] -> File ['/tmp/dir1/dir2/file']
 *
 * is desugared into
 *
 * File ['/tmp/dir1'] -> File['/tmp/dir1/dir2']
 * File ['/tmp/dir1/dir2'] -> File['/tmp/dir1/dir2/file']
 *
 * in-attribute ('before', 'after', 'subscribe', 'notify') dependencies are supposed
 * to be handled at the time of evaluation.
 *
 * TODO : Ignoring refresh events for now
 */


/*
 * Another important desugaring aspect is ResourceDefaults, Collection and
 * ResourceOverriding. Semantically, these are equivalent as ResourceDefaults
 * and Collection overrides the default behaviour of resources of a particular
 * type and ResourceOverriding overrides a particular instance of a type of
 * resource. Changing the default behaviour of resources applies the new property to
 * every instance of that resource and hence overriding a particular instance
 * is a special case which can be desugared similarly to the desugaring of 
 * resource references above. Due to that desugaring, we get a similar kind of 
 * behaviour for overriding as well. Example
 * 
 * File { checksum => md5lite  } # override overrall default file attributes
 * Service ['apache'] { ensure => stopped } # Overriding stop for apache service
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


/*
 * No Brainer :-
 * All branching constructs like switch, selector and if-else
 * desugar into if-else constructs
 */

sealed abstract trait ASTCore
sealed trait ExprC extends ASTCore

// TODO : Precise Types
case object UndefC extends ASTCore // Special value for unassigned variables
case class BoolC (value: Boolean) extends ASTCore
case class StringC (value: String) extends ASTCore
case class TypeC (value: String) extends ASTCore
case class NameC (value: String) extends ASTCore
case class RegexC (value: String) extends ASTCore
case class VariableC (value: String) extends ASTCore
case class BlockStmtC (exprs: List[ASTCore])
case class BranchExprC (test: ExprC, true_br: BlockStmtC, false_br: BlockStmtC) extends ASTCore
case class BinaryExprC (lhs: ExprC, rhs: ExprC, op: BinOp) extends ASTCore
case class NotExprC (oper: ExprC) extends ASTCore
case class FuncAppC (name: ASTCore, args: List[ExprC]) extends ASTCore
case class ImportC (imports: List[String]) extends ASTCore
case class Vardef (variable: ASTCore, value : ExprC , append: Boolean) extends ASTCore
case class OrderResourceC (source: ExprC, target: ExprC, notify: Boolean) extends ASTCore 
case class Attribute (name: ASTCore, value: ExprC, is_append: Boolean)
case class ResourceDeclC (attrs: List[AttributeC]) extends ASTCore
case class ResourceRefC (filter: ExprC) extends ASTCore
case class ResourceOverrideC (ref : ResourceRefC, attrs : List[AttributeC]) extends ASTCore
case class NodeC (hostnames: ASTCore, parent: Option[ASTCore], stmts: List[ASTCore]) extends ASTCore

/* 
 * A class in puppet is a collection of (possibly distinct types) of resources. The
 * parameters add flexibility to the resources in class
 */
case class HostclassC (classname: String, args: List[(VariableC, Option[ExprC])], parent: Option[String], stmts: BlockStmtC) extends ASTCore

/* 
 * A 'define' is like a user-defined resource type and the parameters of a 'define'
 * are like attributes of that resource type
 */
case class DefinitionC (classname: String, args: List[ExprC], stmts: List[ASTCore]) extends ASTCore



object DesugarPuppetAST {

  import scala.collection.immutable._


  private def toAttributeC (typ: Type)  = AttributeC (Name ("type"), typ,   false /* no add */)
  private def toAttributeC (name: Name) = AttributeC (Name ("title"), name, false /* no add */)
  private def toAttributeC (virt: VirtualResType) = virt match {
    case Vrtvirtual => AttributeC (Name ("virtual"), ASTString ("virtual"), false /* no add */)
    case Vrtexported => AttributeC (Name ("virtual"), ASTString ("exported"), false /* no add */)
  }


  private def desugarAST (ast: AST): ASTCore = ast match {

    case ASTBool (b) => BoolC (b)
    case ASTString (s) => StringC (s)
    case Default => // TODO
    case Type (t) => TypeC (t)
    case Name (name) => NameC (name)
    case Undef => UndefC
    case Variable (v) => VariableC (v)
    case Vardef (v, value, append) => VardefC (v, value, append)
    case ASTRegex (r) => RegexC (r)
    case ASTHash (kvs) => // TODO
    case ASTArray (arr) => // TODO
    case HashOrArrayAccess (v, ks) => // TODO
    case BlockStmtDecls (stmts_decls) => BlockStmtC ( stmts_decls.map { desugarAST (_) })
    case BinExpr (lhs, rhs. op) => BinExprC (desugarAST (lhs), desugarAST (rhs), op)
    case NotExpr (oper) => NotExprC (oper)
    case UMinusExpr (oper) => BinExpr (Name ("-1"), oper, Mult)

    
    case RelationExpr (lhs, rhs, op) => // TODO

    case Attribute (name, value, add) => AttributeC (desugarAST (name), desugarAST (value), add)

    case ResourceInstance (title, params) => {
      // Desugar into a ResourceC adding 'title' as another attribute
      val paramsC = params.map { desugarAST (_) }
      val attr = toAttributeC (title)
      ResourceDecl (attr :: paramsC)
    }

    case Resource (typ, instances) => {
      // Desugar into a ResourceC while adding 'type' as another attribute
      val attr = toAttributeC (Type (capitalize (typ)))
      instances.map { attr :: desugar (_) }
    }

    case VirtualResource (res, tvirt) => {
      // Add virtual as an attribute to resource
      val resources = desugarAST (res)
      val attr = toAttribute (tvirt)
      resources.map { case ResourceDeclC (attrs) => ResourceDeclC (attr :: attrs) }
    }
 
    case ResourceRef (typ, titles) => typ match {
      // Name is effectively a type, see the corresponding production rule
      case Name (name) => Type (capitalize (name))
      case typ => typ
    }
    case CollectionExpr (lhs, rhs, op) => // TODO
    case Collection (typ, collexpr, restype, params) => // TODO 
    case ResourceOverride (ref, params) => // TODO
    case ResourceDefaults (typ, params) => {
      val filter = BinExprC (NameC ("type"), TypeC (capitalize (typ)), Equal)
      // TODO : Reconsider
      ResourceOverrideC (ResourceRefC (List (filter)), params.map { desugarAST (_) })
    }

    case IfExpr (test, true_exprs, false_exprs) =>
      IfExprC (desugarAST (test), desugarAST (true_exprs), desugarAST (false_exprs))

    case CaseOpt (values, exprs) => failure ("Unreachable")

    case CaseExpr (test, caseopts) => {

      // Separate 'default' case expression
      def is_default (co: CaseOpt) = match co.value {
        case Default => true
        case _ => false
      }
      val p = caseopts.partition (is_default)
      val default_caseopt  = p._1
      val regular_caseopts = p._2

      // Desugar "regular" case options to if-else constructs
      regular_caseopts.map {
        case CaseOpt (values, exprs) => values.foldLeft (desugarAST (test)) => 
      }
    }

    case Selector (param, values) => 

    case Node (hostnames, None, stmts) => 
      NodeC (desugarAST (hostnames), None, desugarAST (stmts))
    case Node (hostnames, Some (parent), stmts) => 
      NodeC (desugarAST (hostnames), Some (desugarAST (parent)), desugarAST (stmts))

    case Hostclass (classname, args, parent, stmts) => 
      HostclassC (classname,
                  args.map { case (v, None)     => (desugarAST (_), None)
                             case (v, Some (e)) => (desugarAST (_), Some (desugarAST (e))) },
                  desugarAST (stmts))

    case Definition (classname, args, stmts) => 
      DefinitionC (classname, args.map { desugarAST (_) }, desugarAST (stmts))

    case Function (name, args, _) => FuncAppC (desugarAST (name), args.map { desugarAST (_) })
    case Import (imports) => ImportC (imports)
  }
}
