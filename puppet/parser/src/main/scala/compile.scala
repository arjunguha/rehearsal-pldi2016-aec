package puppet.core.eval

import puppet.core._
import scala.util.matching.Regex

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



// TODO : This is directly ported from puppet and is very imperative for now
class Catalog {

  // Lazy compilation: collect and compile
  var classes:     List[(HostclassC, ScopeChain)]
  var definitions: List[(DefinitionC, ScopeChain)]

  type Filter = Map[String, PuppetValue /* TODO: should rather be a subtype of PuppetValue */]
  type Attrs = Map[String, PuppetValue /* all values */]
  type Override = (Filter, Attrs)
  type Collection  = Filter
  type ResourceRef = Filter

  var resources:   List[Resource]
  var overrides:   List[Override]
  var collections: List[Collection]
  var orderings:   List[(ResourceRef, ResourceRef)]

  def add_resource (attrs: Attrs) {
    // check if defined type then add definitions and a list of params
  }

  def add_evaled_resource (res: Resource) {
    resources = res :: resources
  }



  def to_graph () /* scala-graph */ = {
    /*
    eval_classes ()
    eval_generators ()
    finish ()
    */
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
    case RegexV (_) => throw new Exception ("Cannot convert a regex to bool")
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
      Left (nodes.map ({ case node => {
        catalog = new Catalog ()
        val env = eval_toplevel (ast, catalog)
        eval_node (node.name, node.stmts, env, catalog)

        catalog.eval_classes ()
        catalog.eval_collections ()
        catalog.eval_definitions ()
        catalog.eval_overrides ()
        catalog.eval_relationships ()
        catalog
      }}))
    }
    else
    {
      val catalog = new Catalog ()
      val env = eval_toplevel (ast, catalog)
      catalog.eval_classes ()
      catalog.eval_collections ()
      catalog.eval_definitions ()
      catalog.eval_relationsihps ()

      Right (catalog)
    }
  }
}
