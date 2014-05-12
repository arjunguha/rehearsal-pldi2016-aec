package puppet;

import scala.collection.mutable.HashMap

// Understand puppet catalog production from AST
// Understand scoping issues
// See evaluation rules for nodes

sealed abstract trait PuppetValue

type ValueHashMap = HashMap[PuppetValue, PuppetValue]
type ValueArray   = Array[PuppetValue]

case object UndefV extends PuppetValue
case class BoolV (value: Boolean) extends PuppetValue
case class StringV (value: String) extends PuppetValue
case class RegexV (value: Regex) extends PuppetValue
case class ASTHashV (value: ValueHashMap) extends PuppetValue
case class ASTArrayV (value: ValueArray) extends PuppetValue
/* TODO : Resource should be a value
 * case class ResourceV (value: 
 */



/*
 * Properties of scopes
 *
 * The following kind of scopes are possible in puppet
 *
 * 1) Top level scope
 * 2) Node level scope
 * 3) Parent Scope
 * 4) Local Scope
 * 
 * Every Scope has only one parent
 *
 * Class definition creates a named scope whose name is the same as the class's name
 * 
 * Top scope is a named scope
 *
 * Node scope and local scopes created by defined resources and anonymous and cannot
 * be directly refrenced
 *
 * REFERENCING OUT OF SCOPE VARIABLES
 * Variables declared in named scopes can be referenced directly from anywhere 
 * (Including scopes hat otherwise would not have access to them) by using their
 * global qualified name.
 * Out of scope variables are available in other scopes subject to their declaration
 * (Parse order dependence)
 *
 * Variables declared in anonymous scopes can only be accessed normally and do not
 * have global qualified names.
 *
 * Parent scope is only assigned by class inheritance (using the inherits keyword)
 * Any derived class receives the contents of its base class in addition to the 
 * contents of node and top scope
 *
 * Nodes can be inherited similar to classes and similar scope inheritance rules
 * apply to them as well.
 *
 * Appending to any variable referenced from outside the local scope would be
 * treated as a new variable definition in current scope 
 */

object PuppetScope {

  type ScopeRef = String

  private class Scope {

    type Env = Map[String, PuppetValue]

    private val env = Env ()

    def setvar (varname: String, value: Puppetvalue) = env += (varname, value)
    def getvar (varname: String): PuppetValue = env getOrElse (varname, UndefV)
  }

  private val named_scopes = Map [ScopeName, Scope.Env] ("__toplevel__", new Scope)

  private def scope_exists (name: String): Boolean = {
    (Try (named_scopes (name))).map (true) getOrElse false
  }

  def createNamedScope (name: String): ScopeRef = {

    if (scope_exists (name)) throw new Exception ("Scope by this name already exists")

    named_scopes += (name, new Scope ())
    name
  }

  // TODO : Have to be consistent be createNamedScope
  def createEphemeralScope (): Scope = { new Scope }

  private def getScopeByName (name: String): Scope = named_scopes (name)

  val toplevel = named_scopes ("__toplevel__")


  def setvar (ref: ScopeRef, varname: String, value: PuppetValue): Try[Unit] = {

    Try (getScopeByName (ref).setvar (varname, value))
  }

  def getvar (ref: ScopeRef, varname: String): Try[PuppetValue] = {

    Try (getScopeByName (ref).getvar (varname))
  }
}


// TODO : Probably wrap in object
class ScopeChain {

  val scopes: List[PuppetScope.ScopeRef]

  val getvar (varfqname: String): PuppetValue = {

    // TODO
  }

  val setvar (varfqname: String, value: PuppetValue) = {

    // TODO
  }

  val addScope (scoperef: PuppetScope.ScopeRef): Scopechain = {
    val x = new ScopeChain
  } 
}



// TODO : Collection of puppet pre-defined functions
/*
object <funcname> {

  def apply (args): PuppetValue {

  }
}
*/


object PuppetCompile {

      
  private def puppetvalue_to_bool (v: PuppetValue): Boolean = v match {

    /* Puppets idiosyncracies on what can be (automatically) coerced
     * into a bool
     */
    case UndefV => false
    case BoolV (b) => b
    case StringV (s) => ! (s == "" || s == "\"\"" || s == "''") // Empty strings are false
    case RegexV => throw new Exception ("Cannot convert a regex to bool")
    case ASTHashV (_) | ASTArrayV (_) => true // Any hash or array, even empty ones are boolean true
  }

  import scala.util.Try
   
  private def puppetvalue_to_double (v: PuppetValue): Try[Double] = v match {
    case StringV (s) => Try (s.toDouble)
    case _ => throw new Exception ("Cannot convert to double")
  }
  
  private def puppetvalue_to_int (v: PuppetValue): Try[Int] = v match {
    case StringV (s) => Try (s.ToInt) // TODO: Not supporting hex and octal for now 
    case _ => throw new Exception ("Cannot convert to Integer")
  }

  import scala.util.Either
  private def puppetvalue_to_num (v: PuppetValue): Either [Double, Int] = {

    // Cases : Octal, Hexadecimal, Decimal (Negative, Positive), Double (Scientific, negative, positive)
    // First try to parse Octal, if it fails then hex then decimal else double
    val n = puppetalue_to_int (v)
    if (n.isSuccess) Right (n.get) else Left (puppetvalue_to_double (v).get)
  }


  private def eval_op (lhs: PuppetValue,
                       rhs: PuppetValue,
                       op: BinOp): PuppetValue = op match {


    // Takes in boolean operands or operands that can be converted to boolean
    case Or          => BoolV (puppetvalue_to_bool (lhs) || puppetvalue_to_bool (rhs))
    case And         => BoolV (puppetvalue_to_bool (lhs) && puppetvalue_to_bool (rhs))

    // XXX: All integer related operations have to follow ruby semantics and its flexibility/limitations

    // comparison operators: takes operands of several data types and resolve to Boolean
    case GreaterThan => {
      val lhsn = puppetvalue_to_num (lhs)
      val rhsn = puppetvalue_to_num (rhs)
      BoolV (lhsn > rhsn)
    }
    case GreaterEq   => {
      val lhsn = puppetvalue_to_num (lhs)
      val rhsn = puppetvalue_to_num (rhs)
      BoolV (lhsn >= rhsn)
    }

    case LessThan    => {
      val lhsn = puppetvalue_to_num (lhs)
      val rhsn = puppetvalue_to_num (rhs)
      BoolV (lhsn < rhsn)
    }

    case LessEq      => {
      val lhsn = puppetvalue_to_num (lhs)
      val rhsn = puppetvalue_to_num (rhs)
      BoolV (lhsn <= rhsn)
    }

    // TODO : Define equality
    case NotEqual    =>
    case Equal       =>

    // Arithmetic operators, Takes in numbers and resolve to Numbers
    case LShift      => {
      val lhsn = puppetvalue_to_num (lhs)
      val rhsn = puppetvalue_to_num (rhs)

      /*
       * Being ruby compliant, when we ask for left shift by a negative
       * number, ruby does a right shift by its absolute value
       */
      if (rhsn < 0) lhsn >> Math.abs (rhsn)
      else lhsn << rhsn
    }

    case RShift      => {
      val lhsn = puppetvalue_to_num (lhs)
      val rhsn = puppetvalue_to_num (rhs)

      /* Being ruby compliant, when we ask for right shift by a negative
       * number, ruby does a right shift by its absolute value
       */
      if (rhsn < 0) lhsn << Math.abs (rhsn)
      else lhsn >> rhsn
    }

    case Plus        => {
      val lhsn = puppetvalue_to_num (lhs)
      val rhsn = puppetvalue_to_num (rhs)
      
      lhsn + rhsn
    }

    case Minus       => {
      val lhsn = puppetvalue_to_num (lhs)
      val rhsn = puppetvalue_to_num (rhs)

      lhsn - rhsn
    }

    case Div         => {
      val lhsn = puppetvalue_to_num (lhs)
      val rhsn = puppetvalue_to_num (rhs)

      lhsn / rhsn
    }

    case Mult        => {
      val lhsn = puppetvalue_to_num (lhs)
      val rhsn = puppetvalue_to_num (rhs)

      lhsn * rhsn
    }

    case Mod         => {
      val lhsn = puppetvalue_to_num (lhs)
      val rhsn = puppetvalue_to_num (rhs)

      lhsn % rhsn
    }


    // Regex related match, string is left operand and regular expression as right operand, returns a boolean
    case Match       => {
      val lhsstr   = puppetval_to_string (lhs)
      val rhsregex = puppetal_to_regex (rhs)

      // Check for any match
      rhsregex.findFirstIn (lhsstr) match {
        case Some (_) => BoolV (false)
        case None     => BoolV (true)
      }
    }

    case NoMatch     => {
      val lhsstr   = puppetval_to_string (lhs)
      val rhsregex = puppetal_to_regex (rhs)

      // Check for any match
      rhsregex.findFirstIn (lhsstr) match {
        case Some (_) => BoolV (false)
        case None     => BoolV (true)
      }
    }

    case In          => {

      // lhs has to be a string
      lhsstr = puppetval_to_string (lhs)

      // rhs could be either a String, Array or Hashes
      rhs match {
        case StringV (value) => /* Check if lhsstr is a substring */ BoolV (value contains lhsstr)
        case ASTArrayV (arr) => /* Check if any array element is identical to left operand */ BoolV (arr contains lhs)
        case ASTHashV (hash) => /* Check if any key is identical to left operand */ BoolV (hash contains lhs)

        // TODO : Position in error
        case _ => throw new Exception ("Type error: \"in\" expects a string, array or hash")
      }
    }
  }


  private def interpolate (str: String,
                           env: Environment): String = {
    // TODO
    // See puppet interpolation
    throw new Exception ("YTD")
  }



    
  private def eval (ast: ASTCore, env: Environment): PuppetValue = ast match {

    case UndefC          => UndefV
    case BoolC (value)   => BoolV (value)
    case StringC (value) => StringV (interpolate (value))
    case TypeC (value)   => StringV (value) // XXX: Not sure
    case NameC (value)   => StringV (value) // XXX: Not sure
    case RegexC (value)  => RegexV (Regex (value.r))

    case ASTHashC (kvs) => {
      var hashmap = new ValueHashMap ()
      kvs.foreach ({ case (k, v) => hashmap ++ (eval (k, env), eval (v, env))})
      ASTHashV (hashmap)
    }

    case ASTArrayC (arr) => ASTArrayV (arr.map (eval (_, env)).toArray)
    case HashOrArrayAccessC (variable, keys) => /* lookup variable and apply key */
    case VariableC (value) => /* lookup variable and apply key */
    case BlockStmtC (exprs) =>
    case IfElseC (test, true_br, false_br) =>
    case BinExprC (lhs, rhs, op) => eval_op (eval (lhs), eval (rhs), op)
    case NotExprC (oper) => BoolV (! puppetvalue_to_bool (eval (oper)))
    case FuncAppC (name, args) => /* TODO : lookup predefined set of functions */
    case ImportC (imports) =>
    case VardefC (variable, value, append) =>
    case OrderResourceC (source, target, refresh) =>
    case AttributeC (name, value, is_append) =>
    case ResourceDeclC (attrs) =>
    case ResourceRefC (filter) =>
    case ResourceOverrideC (ref, attrs) =>
    case NodeC (hostnames, parent, stmts) =>
    case HostclassC (classname, args, parent, stmts) =>
    case DefinitionC (classname, args, stmts) =>
  }


  class Resource (val typ: String, /* TODO : Odd for now, resolve later */
                  val name: String,
                  val scope: PuppetScope.ScopeRef) {

    var evaluated: Boolean = false

    def evaluate () {

      if (!evaluated) {
        evaluated = true
        // If its not a class then evaluate
        if (typ != "class") {

          /* TODO:
           * 1. Pull out resoure from type collection
           * 2. If resource has parent then evaluate parent
           * 3. Form the scope for evaluation of resource (toplevel + node + parent + local
           * 4. Eval resource element by element
           */
        }
      }
    }
  }


  val resource_overrides = Map [Source, Target]
  val collections = List[Collection]
  val relationships = List[Source, Target]
  val catalog = new Catalog ()
  val topscope = PuppetScope.toplevel
  var resources = List[Resource] () // Local resource array to maintain resource ordering


  val resources = List[Resource] ()

  // TODO: Should give a type collection object
  def import_ast (ast: ASTCore) { ast match {
    case BlockStmtC (stmts) => stmts.foreach (import_ast)
    case node: NodeC => TypeCollection.add_node (node)
    case hc: HostclassC => TypeCollection.add_hostclass (hc); hc.stmts.foreach (import_ast)
    case defn: DefinitionC => TypeCollection.add_definition (defn)
    case _ => Unit ()
  }}


  def init_node_environment () {
    
    val facter_env = Cmd.exec ("facter").get
    facter_env.lines.foreach ({
      case line => {
        val kv = line.split ("=>").map (_.trim)
        PuppetScope.setvar (toplevelscope, kv(0), StringV (kv(1)))
      }
    })
  }


  def add_resource (scope: PuppetScope.ScopeRef, resource: Resource) {

    resources = resource :: resourses
    catalog.add_resource (resource)

    // TODO : If resource type is not class and resource has stage parameter then error that only classes can set stage

    // TODO : If resource is not a class then add a edge to the class that contains this resource.

  }

  def eval_collections () {

  }

  def eval_definitions () {
  }


  def eval_generators () {
    eval_collections ()
    eval_definitions ()
  }

  def eval_classes (klass: List[HostclassC], scope: ScopeChain, lazy_evaluate: Boolean, fqname: Boolean) {

    /* TODO :
     * 1. Find class from TypeCollection, raise error if not found
     * 2. catalog.ensure_in_catalog (klass)
     * 3. Create and save scope of class
     * 4. if lazy_evaluate is not set then setup scope chain and evaluate class
     */
  }

  def eval_node_classes () {
    
    // What are node classes?
    
    /* TODO : evaluate all of the node classes 
     * filter ast for node in classes with params and classes without params
     * evaluate_classes (resources_without_params)
     * evaluate_classes (resources_with_params)
     */
  }


  def eval_ast_node (name: Option[String]) {

    if (TypeCollection.nodes_present) {

      val node = TypeCollection.find_node_by_name (name getOrElse "default").get

      catalog.ensure_in_catalog (node)

      val resource = new Resource ("node", node.name, PuppetScope.createNamedScope (node.name))

      add_resource (PuppetScope.getScopeByName (node.name), resource)

      resource.evaluate ()
    }
  }


  def eval_main () {

    val main_resource = new Resource ("class", 'main, topscope)
    add_resource (topscope, main_resource)
    main_resource.evaluate ()
  }


  def compile (ast: BlockStmtC): Either[List[NodeName, Catalog], Catalog] = {

    /* TODO : Handle Staging in puppet
     * Add main to catalog
     * catalog.add_resource (Resource ("stage", 'main, topscope)
     */

    ast.stmts.map ( { case hc: HostclassC => TypeCollection.add_hostclass (hc); hc.stmts.map (apply) })
    ast.stmts.filter (_.isIntanceOf[DefinitionC]).foreach (TypeCollection.add_definition)
    val nodes = ast.stmts.filter (_.isInstanceOf[NodeC])

    // Wrap in original hostclass for main
    import_ast (HostClassC ('main, List (), None, ast))
    init_node_environment ()
    eval_main ()
    eval_ast_node ()
    eval_node_classes ()
    eval_generators ()
    finish ()
  }
}



object TypeCollection {

  // mutable objects
  private val nodes       = List[NodeC] () // It has to be a list to find the first defined match
  private val hostclasses = Map [String, HostclassC] ()
  private val definitions = Map [String, DefinitionC] ()

  private def hostclass_exists (classname: String): Boolean = {
    (Try (hostnames (classname))).map (true) getOrElse false
  }

  private def definition_exists (classname: String): Boolean = {
    (Try (hostnames (classname))).map (true) getOrElse false
  }

  def add_hostclass (hc: HostclassC) {

    if (definition_exists (hc.classname)) throw new Exception ("Class by this name already exists")

    val merged = hostclasses.get (hc.classname) match {

      case Some (other_hc) => 
        if (other.hc.parent == hc.parent) HostclassC (hc.classname, hc.args, hc.parent, stmts.exprs.append (other_hc.exprs))
        else throw new Exception ("Cannot merge two hostclasses inheriting different parents")

      case None => hc
    }

    hostclasses += (merged.classname, merged)
  }


  def add_node (node: NodeC) {
    if (nodes.exists (node.hostname == _.hostname)) throw new Exception ("Duplicate node")
    else nodes = node :: nodes
  }

  def add_definition (definition: DefinitionC) {

    if (definition_exists (definition.classname) || hostclass_exists (definition.classname))
      throw new Exception ("Duplicate definition, either a class or definition by this name already exists")
    else
      definitions += (definition.classname, definition)
  }

  def nodes_present (): Boolean = nodes.length > 0

  def find_node_by_name (name: String): NodeC {
    // Reverse is important for ordering
    nodes.reverse.find (...)
  }
}
