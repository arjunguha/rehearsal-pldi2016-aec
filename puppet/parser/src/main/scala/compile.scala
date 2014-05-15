package puppet.core.eval

import puppet.core._
import puppet.syntax._
import puppet.util._

import scala.util.matching.Regex
import scalax.collection.Graph
import scalax.collection.GraphEdge._
import scalax.collection.GraphPredef._

object PuppetFunction {

  def apply (fname: String, args: PuppetValue*): PuppetValue = {
    throw new Exception ("feature not supported yet")
  }
}


class Resource (val kind: String, // TODO : Odd for now, resolve later
                val title: String, // Combination of type of resource + its name
                val params: Map[String, PuppetValue],
                val scope: ScopeChain) {

  // Both type and title attribute should be present and the combination should be unique
}


class Catalog {

  // Lazy compilation: collect and compile
  var classes:     List[(HostclassC, ScopeChain)] = List ()
  var definitions: List[(DefinitionC, ScopeChain)] = List ()

  type Filter = ASTHashV /* Map[String, PuppetValue TODO: should rather be a subtype of PuppetValue] */
  type Attrs = Map[String, PuppetValue /* all values */]
  type Override = (Filter, Attrs)
  type Collection  = Filter
  type ResourceRef = Filter

  var resources:   List[Resource] = List ()
  var overrides:   List[Override] = List ()
  var collections: List[Collection] = List ()
  var orderings:   List[(ResourceRef, ResourceRef)] = List ()

  def add_resource (res: Resource) {
    // TODO : Check for duplicates
    resources = res :: resources
  }

  def add_resource (attrs: ASTHashV) {
    val mp = attrs.value.map ({ case (k: StringV, v) => (k.value.toLowerCase -> v) })

    // Name and type of resource are unique 
    val res_typ = mp ("type")
    val res_name = mp ("title")
    add_resource (new Resource ("Resource", res_typ + "::" + res_name, mp, new ScopeChain ()))
  }

  def add_override (filter: Filter, attrs: Attrs) {
    throw new Exception ("feature not supported yet")
  }

  def add_relationship (src: ASTHashV, dst: ASTHashV, refresh: Boolean) {
    orderings = (src, dst) :: orderings
  }

  private def resourceref_to_resource (ref: ASTHashV): Resource = {
    val res = resources.find ({ 
      case res => ref.value.forall ({ 
        case (k, v) => res.params.contains (k.value) && res.params (k.value) == v 
      }) 
    })

    res getOrElse (throw new Exception ("Not found"))
  }


  def to_graph (): Graph[Resource, DiEdge] = {

    val rels = orderings.map ({ case (x, y) => resourceref_to_resource (x) ~> resourceref_to_resource (y) })
    Graph.from (resources, rels)
  }

  def eval_overrides () {
    throw new Exception ("feature not supported yet")
  }

  def eval_classes () {
    throw new Exception ("feature not supported yet")
  }

  def eval_collections () {
    throw new Exception ("feature not supported yet")
  }

  def eval_definitions () {
    throw new Exception ("feature not supported yet")
  }

  def eval_relationships () {
    throw new Exception ("feature not supported yet")
  }
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
    case StringV (s) => Try (s.toInt) // TODO: Not supporting hex and octal for now 
    case _ => throw new Exception ("Cannot convert to Integer")
  }

  import scala.util.Either
  private def puppetvalue_to_num (v: PuppetValue): Either [Double, Int] = {

    // Cases : Octal, Hexadecimal, Decimal (Negative, Positive), Double (Scientific, negative, positive)
    // First try to parse Octal, if it fails then hex then decimal else double
    val n = puppetvalue_to_int (v)
    if (n.isSuccess) Right (n.get) else Left (puppetvalue_to_double (v).get)
  }

  private def puppetvalue_to_string (v: PuppetValue): String = v match {
    case UndefV => ""
    case BoolV (b) => if (b) "true" else "false"
    case StringV (s) => s
    case RegexV (r) => r.toString
    case ASTArrayV (arr) => arr.foldLeft ("") ({ case (acc, elem) => acc + puppetvalue_to_string (elem) })
    case ASTHashV (hash) => hash.foldLeft ("") ({ case (acc, elem) => acc + puppetvalue_to_string (elem._1) +
                                                                            puppetvalue_to_string (elem._2) })
  }



  /*
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
    */

      /*
       * Being ruby compliant, when we ask for left shift by a negative
       * number, ruby does a right shift by its absolute value
       */
      /*
      if (rhsn < 0) lhsn >> Math.abs (rhsn)
      else lhsn << rhsn
    }

    case RShift      => {
      val lhsn = puppetvalue_to_num (lhs)
      val rhsn = puppetvalue_to_num (rhs)
    */

      /* Being ruby compliant, when we ask for right shift by a negative
       * number, ruby does a right shift by its absolute value
       */
      /*
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
        case StringV (value) => */ /* Check if lhsstr is a substring */ /* BoolV (value contains lhsstr) */
        /* case ASTArrayV (arr) => */ /* Check if any array element is identical to left operand */ /* BoolV (arr contains lhs) */
        /* case ASTHashV (hash) => */ /* Check if any key is identical to left operand */ /* BoolV (hash contains lhs) */

        // TODO : Position in error
        /* case _ => throw new Exception ("Type error: \"in\" expects a string, array or hash")
      }
    }
  }
  */


  private def interpolate (str: String,
                           env: ScopeChain): String = {
    // TODO: interpolate!!
    str
  }

  // TODO : "$" could be stripped at parser stage rendering this function obsolete
  private def variable_to_string (variable: VariableC): String = {
    variable.value.stripPrefix ("$")
  }

  private def merge_hash (lhs: ASTHashV, rhs: ASTHashV): ASTHashV = {
    ASTHashV ((lhs.value.toList ::: rhs.value.toList).toMap)
  }

  private def resourceprops_to_ref (attrs: ASTHashV): ASTHashV = {
    val mp = attrs.value.map ({ case (k: StringV, v) => (k.value.toLowerCase -> v) })

    // Name and type of resource are unique 
    val res_typ = mp ("type")
    val res_name = mp ("title")

    ASTHashV (Map (StringV ("type") -> res_typ, StringV ("title") -> res_name))
  }


  // TODO : Catalog is fixed, can be curried away
  // TODO : More precise type than puppet value
  private def eval (ast: ASTCore, env: ScopeChain, catalog: Catalog): PuppetValue = ast match {

    case UndefC          => UndefV
    case BoolC (value)   => BoolV (value)
    case StringC (value) => StringV (interpolate (value, env))
    case TypeC (value)   => StringV (value) // XXX: Not sure
    case NameC (value)   => StringV (value) // XXX: Not sure
    case RegexC (value)  => RegexV (new Regex (value))

    case ASTHashC (kvs) => ASTHashV (kvs.map ({ case (k, v) => (eval (k, env, catalog).asInstanceOf[StringV], eval (v, env, catalog)) }).toMap)

    case ASTArrayC (arr) => ASTArrayV (arr.map (eval (_, env, catalog)).toArray)
    case HashOrArrayAccessC (variable, keys) => /* TODO: lookup variable and apply key */ throw new Exception ("HashOrArrayAccess not evaluated")
    case VariableC (value) => env.getvar (value) getOrElse UndefV

    case BlockStmtC (exprs) => {

      val scope = PuppetScope.createEphemeralScope ()
      val new_env = env.addScope (scope)
      // Return the last evaluated value
      exprs.map (eval (_, new_env, catalog)).head
      // XXX: Maybe destroy newly created ephemeral scope
    }

    case IfElseC (test, true_br, false_br) => {
      if (puppetvalue_to_bool (eval (test, env, catalog)))
        eval (true_br, env, catalog)
      else
        eval (false_br, env, catalog)
    }

    case BinExprC (lhs, rhs, op) => throw new Exception ("feature not supported yet")
    case NotExprC (oper) => BoolV (! puppetvalue_to_bool (eval (oper, env, catalog)))
    case FuncAppC (name, args) => PuppetFunction (puppetvalue_to_string (eval (name, env, catalog)),  args.map (eval (_, env, catalog)).toSeq:_*)
    case ImportC (imports) => throw new Exception ("Feature not supported yet")

    // TODO :Get Rid of coercing: More stronger types
    case VardefC (variable, value, append) => {
      val puppet_value = eval (value, env, catalog)
      env.setvar (variable_to_string (variable.asInstanceOf[VariableC]), puppet_value, append)
      puppet_value
    }

    case OrderResourceC (source, target, refresh) => {
      val lhs = eval (source, env, catalog).asInstanceOf[ASTHashV]
      val rhs = eval (target, env, catalog).asInstanceOf[ASTHashV]
      catalog.add_relationship (lhs, rhs, refresh)
      rhs
    }


    case AttributeC (name, value, is_append) =>
      if (is_append) throw new Exception ("Appending of attributes is not supported yet")
      else  ASTHashV (Map (eval (name, env, catalog).asInstanceOf[StringV] -> eval (value, env, catalog)))

    case ResourceDeclC (attrs) => {
      val listhash = attrs.map (eval (_, env, catalog)) collect ({ case x: ASTHashV => x })
      val singlehash = listhash.reduce (merge_hash)
      catalog.add_resource (singlehash)
      resourceprops_to_ref (singlehash)
      // Should return a subset of attributes to identify this resource: basically type and title
    }

    case ResourceRefC (filter) => /* filter.map (eval (_, env, catalog)).collect ({ case x: ASTHashV => x}).reduce (merge_hash (_, _)) */
      throw new Exception ("Resource references not supported yet")
    case ResourceOverrideC (ref, attrs) => throw new Exception ("Feature not supported yet") // catalog.add_override ()

    // TODO : Bad, convert into partial function
    case _ => UndefV
  }


  def eval_node (name: String, ast: BlockStmtC, env: ScopeChain, catalog: Catalog) {

    // Setup node scope
    val node_scope = PuppetScope.createNamedScope (name)
    val env_new = env.addScope (node_scope)

    ast.exprs.foreach (eval (_, env_new, catalog))
  }

  def eval_toplevel (ast: BlockStmtC, catalog: Catalog): ScopeChain = {

    val toplevel_scope = PuppetScope.createNamedScope ("")
    val env = (new ScopeChain ()).addScope (toplevel_scope)

    val facter_env = Cmd.exec ("facter").get
 
    facter_env.lines.foreach ({ case line => {
        val kv = line.split ("=>").map (_.trim)
        if (kv.length > 1 // TODO : Hack to get past the failing smoke test for now
) env.setvar (kv(0), StringV (kv(1)))       }
    })
  
    val main_resource = new Resource ("class", 'main.toString, Map[String, PuppetValue] (), env)
    catalog.add_resource (main_resource)
    
    ast.exprs.foreach (eval (_, env, catalog))
    env
  }


  def compile (ast: BlockStmtC): Either[List[(String, Catalog)], Catalog] = {

    import puppet.core.eval.PuppetCompositeValueTypes._

    /* TODO : Handle Staging in puppet
     * Add main to catalog
     * catalog.add_resource (Resource ("stage", 'main, topscope)
     */

    TypeCollection.add (HostclassC ('main.toString, List (), None, ast))

    def f (s: ASTCore): Unit = s match {
      case hc:   HostclassC => TypeCollection.add (hc); hc.stmts.asInstanceOf[BlockStmtC].exprs.foreach (f)
      case defn: DefinitionC => TypeCollection.add (defn)
      case _ => ()
    }
    ast.exprs.foreach (f)

    // Filtering + Type extraction via partial function
    val nodes = ast.exprs.collect ({ case node: NodeC => node })
    if (nodes.exists (!_.parent.isEmpty))
      throw new Exception ("Node inheritance not supported, deprecated by Puppet")

    // Wrap in original hostclass for main
    if (nodes.length > 0)
    {
      Left (nodes.map ({ case node => {
        val catalog = new Catalog ()
        val env = eval_toplevel (ast, catalog)
        val nodename = puppetvalue_to_string (eval (node.hostname, env, catalog))

        // TODO: Bad Type coercion
        eval_node (nodename, node.stmts.asInstanceOf[BlockStmtC], env, catalog)

        catalog.eval_classes ()
        catalog.eval_collections ()
        catalog.eval_definitions ()
        catalog.eval_overrides ()
        catalog.eval_relationships ()
        (nodename, catalog)
      }}))
    }
    else
    {
      val catalog = new Catalog ()
      val env = eval_toplevel (ast, catalog)
      /*
      TODO 
      catalog.eval_classes ()
      catalog.eval_collections ()
      catalog.eval_definitions ()
      catalog.eval_relationships ()
      */

      Right (catalog)
    }
  }
}
