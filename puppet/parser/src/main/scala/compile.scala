package puppet.core.eval

import puppet.core._
import puppet.syntax._
import puppet.util._

import scala.util.matching.Regex
import scalax.collection.Graph
import scalax.collection.GraphEdge._
import scalax.collection.GraphPredef._

/*
 * There are 3 kinds of resources => Stage, Class and a Resource.
 * Stage and Class are meta resources
 */
case class Resource (val kind: String, // TODO : Odd for now, resolve later
                val title: String, // Combination of type of resource + its name
                val params: Map[String, Value]) {

  // Both type and title attribute should be present and the combination should be unique

  def isVirtual (): Boolean = {
    throw new Exception ("Not determined yet")
  }

  def isExported (): Boolean = {
    throw new Exception ("Not determined yet")
  }
}



class Catalog {

  // Lazy compilation: collect and compile
  var classes:     List[(HostclassC, ScopeChain)] = List ()
  var definitions: List[(DefinitionC, ScopeChain)] = List ()

  type Filter = ASTHashV /* Map[String, Value TODO: should rather be a subtype of Value] */
  type Attrs = Map[String, Value /* all values */]
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
    add_resource (new Resource ("Resource", res_typ + "::" + res_name, mp))
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

    val nodes = resources
    val edges = orderings.map ({ case (x, y) => resourceref_to_resource (x) ~> resourceref_to_resource (y) })
    Graph.from (nodes, edges)
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
}


object PuppetCompile {
  
  import scala.util.Try

  /*
   * All integer related operations have to follow ruby semantics and its flexibility/limitations
   *
   * Being ruby compliant, when we ask for left shift by a negative
   * number, ruby does a right shift by its absolute value.
   * Vice Versa for right shift
   */
  private def eval_op (op: BinOp, x: Value, y: Value): Value = op match {

    case Or          => BoolV (x.toBool || y.toBool)
    case And         => BoolV (x.toBool && y.toBool)
    case GreaterThan => BoolV (x.toDouble >  y.toDouble)
    case GreaterEq   => BoolV (x.toDouble >= y.toDouble)
    case LessThan    => BoolV (x.toDouble <  y.toDouble)
    case LessEq      => BoolV (x.toDouble <= y.toDouble)
    case NotEqual    => throw new Exception ("Not supported yet")
    case Equal       => throw new Exception ("Not supported yet")

    case LShift => StringV ((if (y.toInt > 0) x.toInt << y.toInt else x.toInt >> y.toInt).toString)
    case RShift => StringV ((if (y.toInt > 0) x.toInt >> y.toInt else x.toInt << y.toInt).toString)

    case Plus  => StringV (if (Try (x.toInt).isSuccess && Try (y.toInt).isSuccess) (x.toInt + y.toInt).toString
                           else (x.toDouble + y.toDouble).toString)

    case Minus => StringV (if (Try (x.toInt).isSuccess && Try (y.toInt).isSuccess) (x.toInt - y.toInt).toString
                           else (x.toDouble - y.toDouble).toString)

    case Div   => StringV (if (Try (x.toInt).isSuccess && Try (y.toInt).isSuccess) (x.toInt / y.toInt).toString
                           else (x.toDouble / y.toDouble).toString)

    case Mult  => StringV (if (Try (x.toInt).isSuccess && Try (y.toInt).isSuccess) (x.toInt * y.toInt).toString
                           else (x.toDouble * y.toDouble).toString)

    case Mod   => StringV ((x.toInt % y.toInt).toString)

    // Regex related match, string is left operand and regular expression as right operand, returns a boolean
    case Match   => BoolV (!(y.asInstanceOf[RegexV].value findFirstIn x.toPString).isEmpty)
    case NoMatch => BoolV ( (y.asInstanceOf[RegexV].value findFirstIn x.toPString).isEmpty) // TODO : Should have been desugared
    case In      => y match {
      case StringV   (v) => BoolV (v contains x.toPString)
      case ASTArrayV (v) => BoolV (v contains StringV (x.toPString))
      case ASTHashV  (v) => BoolV (v contains StringV (x.toPString))
      case _ => throw new Exception ("\"In\" Operator not supported for types other than String, Array or Hash")
    }
  }


  private def interpolate (str: String,
                           env: ScopeChain): String = {
    // TODO: interpolate!!
    str
  }

  // TODO : "$" could be stripped at parser stage rendering this function obsolete
  private def variable_to_string (variable: VariableC): String = {
    variable.value.stripPrefix ("$")
  }


  private def resourceprops_to_ref (attrs: ASTHashV): ASTHashV = {
    val mp = attrs.value.map ({ case (k: StringV, v) => (k.value.toLowerCase -> v) })

    // Name and type of resource are unique 
    val res_typ = mp ("type")
    val res_name = mp ("title")

    ASTHashV (Map (StringV ("type") -> res_typ, StringV ("title") -> res_name))
  }


  // TODO : Catalog is fixed, can be curried away
  // TODO : More precise type than Value
  private def eval (ast: ASTCore, env: ScopeChain, catalog: Catalog): Value = ast match {

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
      if ((eval (test, env, catalog)).toBool)
        eval (true_br, env, catalog)
      else
        eval (false_br, env, catalog)
    }

    case BinExprC (lhs, rhs, op) => eval_op (op, eval (lhs, env, catalog), eval (rhs, env, catalog))
    case NotExprC (oper) => BoolV (!(eval (oper, env, catalog)).toBool)
    case FuncAppC (name, args) => PuppetFunction ((eval (name, env, catalog)).toPString,  args.map (eval (_, env, catalog)).toSeq:_*)
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
      val singlehash = listhash.reduce (_.append (_))
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

    PuppetScope.clear ()

    val toplevel_scope = PuppetScope.createNamedScope ("")
    val env = (new ScopeChain ()).addScope (toplevel_scope)

    val facter_env = Cmd.exec ("facter").get
 
    facter_env.lines.foreach ({ case line => {
        val kv = line.split ("=>").map (_.trim)
        if (kv.length > 1 // TODO : Hack to get past the failing smoke test for now
) env.setvar (kv(0), StringV (kv(1)))       }
    })
  
    val main_resource = new Resource ("class", 'main.toString, Map[String, Value] ())
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
        val nodename = (eval (node.hostname, env, catalog)).toPString

        // TODO: Bad Type coercion
        eval_node (nodename, node.stmts.asInstanceOf[BlockStmtC], env, catalog)

        catalog.eval_classes ()
        catalog.eval_collections ()
        catalog.eval_definitions ()
        catalog.eval_overrides ()
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
      */

      Right (catalog)
    }
  }
}
