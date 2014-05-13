package puppet;

import scala.collection.mutable.HashMap

// Understand puppet catalog production from AST
// Understand scoping issues
// See evaluation rules for nodes

sealed abstract trait PuppetValue

object PuppetCompositeValueTypes {

  type ValueHashMap = HashMap[PuppetValue, PuppetValue]
  type ValueArray   = Array[PuppetValue]
}

import PuppetCompositeValueTypes._

case object UndefV extends PuppetValue
case class BoolV (value: Boolean) extends PuppetValue
case class StringV (value: String) extends PuppetValue
case class RegexV (value: Regex) extends PuppetValue
case class ASTHashV (value: ValueHashMap) extends PuppetValue
case class ASTArrayV (value: ValueArray) extends PuppetValue


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


// TODO : This should be a class
object PuppetScope {

  type ScopeRef = String

  private class Scope {

    type Env = Map[String, PuppetValue]

    private val env = Env ()

    def setvar (varname: String, value: Puppetvalue) = env += (varname, value)
    def getvar (varname: String): PuppetValue = env (varname)
  }

  private val named_scopes = Map [ScopeName, Scope.Env] ("__toplevel__", new Scope)

  def scope_exists (name: String): Boolean = {
    (Try (named_scopes (name))).map (true) getOrElse false
  }

  def createNamedScope (name: String): ScopeRef = {

    if (scope_exists (name))
      throw new Exception ("Scope by this name already exists")

    named_scopes += (name, new Scope ())
    name
  }

  // XXX: Need not mix ephemeral scopes with named scopes
  def createEphemeralScope (): Scope = { 

    // alphanumeric random string
    val name = Random.alphanumeric.take (8).mkString
    if (scope_exists (name)) createEphemeralScope ()
    else named_scopes += (name, new Scope ())
  }

  private def getScopeByName (name: String): Try[Scope] = named_scopes (name)

  val toplevel = named_scopes ("")

  def setvar (ref: ScopeRef, varname: String, value: PuppetValue) {

    var scope = getScopeByName (ref)

    if (scope.isSuccess) scope.flatMap (_.setvar (varname, value))
    else throw new Exception ("Invalid Scope")
  }

  def getvar (ref: ScopeRef, varname: String): Try[PuppetValue] = {

    var scope = getScopeByName (ref)

    if (scope.isSuccess) scope.flatMap (_.getvar (varname))
    else throw new Exception ("Invalid Scope")
  }
}



class ScopeChain (val scopes: List[PuppetScope.ScopeRef] = List[PuppetScope.ScopeRef] ()) {

  private def is_qualified (name: String): Boolean = ((name indexOf "::") > 0)

  val getvar (varfqname: String): Try[PuppetValue] = {

    if (is_qualified (name)) {

      // Make sure that scopes are valid
      val tokens = (name split "::")
      val scoperefs = tokens.slice (0, tokens.length - 1)
      val varname = tokens (tokens.length - 1)

      if (!scoperefs.forall (PuppetScope.scope_exists))
        throw new Exception ("Invalid scope chain")

      // the last one is variable name, all others are scope names
      Try (PuppetScope.getvar (scoperefs (scorerefs.length - 1), varname))
    }
    else {

      // Order is important
      val foundscope = scopes.find (PuppetScope.getvar (_, varfqname).isSuccess)
      if (!foundscope.isEmpty)
         PuppetScope.getvar (foundscope.get, varfqname)
      else
         Try (throw new Exception ("Variable not found in any scope"))
    }
  }

  def setvar (varfqname: String, value: PuppetValue, append: Boolean = false) {

    // Variable can only be assigned using their short name
    if (!append && is_qualified (varfqname))
      throw new Exception ("Cannot assign a fully qualified variable")

    val cur_scope = scopes.head

    if (append) {

      val old_val = getvar (varfqname)

      if (!old_val.isSuccess)
        throw new Exception ("Cannot append to non existing variable")

      val new_val = (old_val.get, value) match {
        case (StringV (ov), StringV (nv)) => StringV (ov + nv)
        case (ASTHashV (ov), ASTHashV (nv)) => ASTHashV (nv.map ( { case (k,v) => ov += (k -> v) }))
        case (ASTArrayV (ov), ASTArray (nv)) => ASTArrayV (ov.append (nv))
        case _ => throw new Exception ("Type mismatch for append")
      }
    }
    else {
      if (PuppetScope.getvar (cur_scope, varfqname).isSuccess)
        throw new Exception ("Cannot reassign variable")

      PuppetScope.setvar (cur_scope, varfqname, value)
    }
  }

  val addScope (scoperef: PuppetScope.ScopeRef): ScopeChain = {
    new ScopeChain (scoperef :: scopes)
  }
}



// TODO : Collection of puppet pre-defined functions
/*
object <funcname> {

  def apply (args): PuppetValue {

  }
}
*/


class Resource (val typ: String, /* TODO : Odd for now, resolve later */
    val name: String,
    val params: Map[String, String],
    val scope: PuppetScope.ScopeRef,
    val virtual: Boolean) {

  // Both type and title attribute should be present and the combination should be unique
}



class Catalog {

  val resources:   List[Resource]
  val overrides:   List[Override]
  val collections: List[Collection]
  val classes:     List[HostclassC]
  val definitions: List[DefinitionC, Params]
  val orderings:   List[(ResourceRef, ResourceRef)]


  def add_resource (attrs: ) {
    // check if defined type then add definitions and a list of params
  }

  def add_evaled_resource (res: Resource) {
    resources = res :: resources
  }



  def to_graph () /* scala-graph */ = {
    eval_node_classes ()
    eval_generators ()
    finish ()

  }

  def eval_classes () {}
  def eval_collections () {}
  def eval_definitions () {}

  def eval_relationships () {}

}


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

  private def eval (ast: ASTCore, env: ScopeChain, catalog: Catalog): PuppetValue = ast match {

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
    case VariableC (value) => env.lookup (value) getOrElse UndefV

    case BlockStmtC (exprs) => {

      val scope = PuppetScope.createEphemeralScope ()
      val new_env = env.addScope (scope)
      // Return the last evaluated value
      exprs.map (eval (_, new_env, catalog)).head
      // XXX: Maybe destroy newly created ephemeral scope
    }

    case IfElseC (test, true_br, false_br) => {
      if (eval (test, env, catalog).value)
        eval (true_br, env, catalog)
      else
        eval (false_br, env, catalog)
    }

    case BinExprC (lhs, rhs, op) => eval_op (eval (lhs), eval (rhs), op)
    case NotExprC (oper) => BoolV (! puppetvalue_to_bool (eval (oper)))
    case FuncAppC (name, args) => /* TODO : lookup predefined set of functions */
    case ImportC (imports) => /* TODO : Include */
    case VardefC (variable, value, append) => env.setvar (variable, value, append)

    case OrderResourceC (source, target, refresh) => catalog.add_relationship (eval (source, env, catalog),
                                                                               eval (target, env, catalog),
                                                                               refresh)

    case AttributeC (name, value, is_append) => // TODO : Eval attribute
    case ResourceDeclC (attrs) => catalog.add_resource (attrs_ev = attrs.map (eval (_, env, catalog)))
    case ResourceRefC (filter) => // TODO
    case ResourceOverrideC (ref, attrs) => // TODO
  }


  def eval_node (name: String, ast: BlockStmtC, env: ScopeChain, catalog: Catalog) {

    // Setup node scope
    val node_scope = PuppetScope.createNamedScope (name)
    val env_new = env.add (node_scope)

    ast.foreach (eval (_, env_new, catalog))
  }


  def eval_toplevel (ast: BlockStmtC, catalog: Catalog): ScopeChain = {

    val toplevel_scope = PuppetScope.createNamedScope ("")
    val env = (new ScopeChain ()).addScope (toplevel_scope)

    val facter_env = Cmd.exec ("facter").get
 
    facter_env.lines.foreach ({ case line => {
        val kv = line.split ("=>").map (_.trim)
        env.setvar (kv(0), StringV (kv(1)))
      }
    })
  
    val main_resource = new Resource ("class", 'main, env)
    catalog.add_resource (main_resource, env)
    
    ast.foreach (eval (_, env, catalog))
    env
  }


  def compile (ast: BlockStmtC): Either[List[NodeName, Catalog], Catalog] = {

    /* TODO : Handle Staging in puppet
     * Add main to catalog
     * catalog.add_resource (Resource ("stage", 'main, topscope)
     */

    TypeCollection.add (HostclassC ('main, List (), None, ast))
    ast.stmts.map ( { case hc: HostclassC => TypeCollection.add (hc); hc.stmts.map (apply) 
                      case defn: DefinitionC => TypeCollection.add (defn) } )

    val nodes = ast.stmts.filter (_.isInstanceOf [NodeC])
    if (nodes.exists (!_.parent.isEmpty))
      throw new Exception ("Node inheritance not supported, deprecated by Puppet")

    // Wrap in original hostclass for main
    if (nodes.length)
    {
      val catalogs = nodes.map ({ case node => {
        catalog = new Catalog ()
        val env = eval_toplevel (ast, catalog)
        eval_node (node.name, node.stmts, env, catalog)

        catalog.eval_classes ()
        catalog.eval_collections ()
        catalog.eval_definitions ()
        catalog.eval_overrides ()
        catalog.eval_relationships ()
        catalog
      }})

      Left (catalogs)
    }
    else
    {
      catalog = new Catalog ()
      val env = eval_toplevel (ast, catalog)
      catalog.eval_classes ()
      catalog.eval_collections ()
      catalog.eval_definitions ()
      catalog.eval_relationsihps ()

      Right (catalog)
    }
  }
}



object TypeCollection {

  // mutable objects
  private val hostclasses = Map [String, HostclassC] ()
  private val definitions = Map [String, DefinitionC] ()

  private def hostclass_exists (classname: String): Boolean = {
    (Try (hostnames (classname))).map (true) getOrElse false
  }

  private def definition_exists (classname: String): Boolean = {
    (Try (hostnames (classname))).map (true) getOrElse false
  }

  def add (hc: HostclassC) {

    if (definition_exists (hc.classname)) throw new Exception ("Class by this name already exists")

    val merged = hostclasses.get (hc.classname) match {

      case Some (other_hc) => 
        if (other.hc.parent == hc.parent) HostclassC (hc.classname, hc.args, hc.parent, stmts.exprs.append (other_hc.exprs))
        else throw new Exception ("Cannot merge two hostclasses inheriting different parents")

      case None => hc
    }

    hostclasses += (merged.classname, merged)
  }

  def add (definition: DefinitionC) {

    if (definition_exists (definition.classname) || hostclass_exists (definition.classname))
      throw new Exception ("Duplicate definition, either a class or definition by this name already exists")
    else
      definitions += (definition.classname, definition)
  }
}
