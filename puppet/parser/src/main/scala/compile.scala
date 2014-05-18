package puppet.core.eval

import puppet.core._
import puppet.syntax._
import puppet.util._

import scala.collection._
import scala.util.matching.Regex


sealed abstract class Node (title: String)

// TODO : Add staging support
case class Resource (title: String, 
                     params: mutable.Map[String, Value]) extends Node (title) {

  private def depsToResRefs (v: Value): List[ResourceRefV] = {
    v match {
      case v : ASTArrayV => (v.value.toList flatMap depsToResRefs)
      case v : ResourceRefV  => (List (v))
      case _ => throw new Exception ("Value is not a valid resource reference")
    }
  }

  private def attrToResRefs (key: String): List[ResourceRefV] = {
    (params.get (key) map depsToResRefs) getOrElse List ()
  }

  def sources: List[ResourceRefV] = {
    attrToResRefs ("require") ::: attrToResRefs ("subscribe")
  }

  def targets: List[ResourceRefV] = {
    attrToResRefs ("before") ::: attrToResRefs ("notify")
  }

  def mergeAttr (name: String, value: Value, append: Boolean = false) {
    if (append)
      throw new Exception ("Append not supported yet")

    params += (name -> value)
  }
  
  def getAttr (name: String): Option[Value] = params get name

  def isReferredByRef (ref: ResourceRefV): Boolean = {
    PuppetCompile.evalRefOnResource (ref, this)
    // ref.value.forall ({ case (k, v) => (params get k) == Some (v) })
  }

  def toResourceRefV: ResourceRefV = {
    ResourceRefV (ResourceRefV (StringV ("type"), params ("type"), FEqOp),
                  ResourceRefV (StringV ("title"), params ("title"), FEqOp), FAndOp)
  }
}


case class HostClass (title: String) extends Node (title) {}
case class Stage (title: String) extends Node (title) {}


object PuppetCompile {

  def evalRefOnResource (ref: ResourceRefV, resource: Resource): Boolean = ref.op match {
    case FEqOp    => resource.params get ref.lhs.toPString map (_ == ref.rhs) getOrElse false
    case FNotEqOp => resource.params get ref.lhs.toPString map (_ != ref.rhs) getOrElse false
    case FAndOp   => evalRefOnResource (ref.lhs.asInstanceOf[ResourceRefV], resource) &&
                     evalRefOnResource (ref.lhs.asInstanceOf[ResourceRefV], resource)
    case FOrOp    => evalRefOnResource (ref.lhs.asInstanceOf[ResourceRefV], resource) ||
                     evalRefOnResource (ref.lhs.asInstanceOf[ResourceRefV], resource)
  }
  

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
    case NotEqual    => throw new Exception ("Not supported yet") // TODO
    case Equal       => throw new Exception ("Not supported yet") // TODO

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
    case NoMatch => BoolV ( (y.asInstanceOf[RegexV].value findFirstIn x.toPString).isEmpty) // XXX : Should have been desugared
    case In      => y match {
      case StringV   (v) => BoolV (v contains x.toPString)
      case ASTArrayV (v) => BoolV (v contains StringV (x.toPString))
      case ASTHashV  (v) => BoolV (v contains x.toPString)
      case _ => throw new Exception ("\"In\" Operator not supported for types other than String, Array or Hash")
    }
  }


  // TODO: interpolate!!
  private def interpolate (str: String, env: ScopeChain): String = str

  private def resourceASTToTitle (attrs: ASTHashV): String =
    attrs.value ("type").toPString + ":" + attrs.value ("title").toPString

  private def eval (ast: ASTCore, env: ScopeChain, catalog: Catalog, parent: HostClass): Value = {

    // TODO : More precise type than 'Value
    def evalpf (ast: ASTCore, env: ScopeChain): Value = (ast, env) match {

      case (UndefC, _)            => UndefV
      case (BoolC (value), _)     => BoolV (value)
      case (StringC (value), env) => StringV (interpolate (value, env))
      case (TypeC (value),  _)    => StringV (value) // XXX: Not sure
      case (NameC (value),  _)    => StringV (value) // XXX: Not sure
      case (RegexC (value), _)    => RegexV (new Regex (value))
      case (ASTHashC (kvs), _)    => ASTHashV (kvs.map ({ case (k, v) => (evalpf (k, env).asInstanceOf[StringV].value,
                                                                          evalpf (v, env))}).toMap)
      case (ASTArrayC (arr), env) => ASTArrayV (arr.map (evalpf (_, env)).toArray) // TODO : Should have been toArray from beginning
      case (HashOrArrayAccessC (variable, keys), env) => /* TODO: lookup variable and apply key */ throw new Exception ("HashOrArrayAccess not evaluated")
      case (VariableC (value), env) => env.getvar (value) getOrElse UndefV

      case (BlockStmtC (exprs), env) => {
        val scope = PuppetScope.createEphemeralScope ()
        val new_env = env.addScope (scope)
        // Return the last evaluated value
        exprs.map (evalpf (_, new_env)).head
        // XXX: Maybe destroy newly created ephemeral scope
      }

      case (IfElseC (test, true_br, false_br), env) =>
        if ((evalpf (test, env)).toBool) evalpf (true_br, env)
        else evalpf (false_br, env)

      case (BinExprC (lhs, rhs, op), env) => eval_op (op, evalpf (lhs, env), evalpf (rhs, env))
      case (NotExprC (oper), env) => BoolV (!(evalpf (oper, env)).toBool)
      case (FuncAppC (name, args), env) => Function ((evalpf (name, env)).toPString,  args.map (evalpf (_, env)).toSeq:_*)

      // TODO : I dont think that Import should have reached this far, it should have been eliminated earlier
      case (ImportC (imports), _) => throw new Exception ("Feature not supported yet")

      case (VardefC (variable, value, append), _) => {
        val puppet_value = evalpf (value, env)
        env.setvar (variable.asInstanceOf[VariableC].value, puppet_value, append)
        puppet_value
      }

      case (OrderResourceC (source, target, refresh), _) => {
        val lhs = evalpf (source, env).asInstanceOf[ResourceRefV]
        val rhs = evalpf (target, env).asInstanceOf[ResourceRefV]
        catalog.addRelationship (lhs, rhs, refresh)
        rhs
      }

      case (AttributeC (name, value, is_append), env) =>
        if (is_append) throw new Exception ("Appending of attributes is not supported yet")
        else  ASTHashV (immutable.Map ((evalpf (name, env)).asInstanceOf[StringV].toPString -> evalpf (value, env)))

      case (ResourceDeclC (attrs), env) => {
        val params = attrs.map (evalpf (_, env)) map (_.asInstanceOf[ASTHashV]) reduce (_.append (_))
        val resource = Resource (resourceASTToTitle (params), mutable.Map (params.value.toSeq:_*))
        val resourceref = resource.toResourceRefV

        resource.sources.foreach (catalog.addRelationship (_, resourceref))
        resource.targets.foreach (catalog.addRelationship (resourceref, _))
        catalog.addResource (resource, parent)

        resourceref
      }

      case (FilterExprC (lhs, rhs, op), env) => op match {
        case FEqOp    => ResourceRefV (evalpf (lhs, env), evalpf (rhs, env), FEqOp)
        case FNotEqOp => ResourceRefV (evalpf (lhs, env), evalpf (rhs, env), FNotEqOp)
        case FAndOp   => ResourceRefV (evalpf (lhs, env), evalpf (rhs, env), FAndOp)
        case FOrOp    => ResourceRefV (evalpf (lhs, env), evalpf (rhs, env), FOrOp)
      }

      case (ResourceOverrideC (ref, attrs), env) => { 
        val refv = evalpf (ref, env)
        val params = (attrs map (evalpf (_, env)) map (_.asInstanceOf[ASTHashV]) reduce (_.append (_)))
        catalog.addOverride (refv.asInstanceOf[ResourceRefV], params.value)
        UndefV // return value, dont know what to return
      }
      
      // TODO : Partial function
      case _ => UndefV
    }

    evalpf (ast, env)
  }
  

  def evalNode (name: String, block: ASTCore, env: ScopeChain, catalog: Catalog, parent: HostClass) {

    // Setup node scope
    val node_scope = PuppetScope.createNamedScope (name)
    val env_new = env.addScope (node_scope)

    eval (block, env_new, catalog, parent)
  }

  def evalToplevel (block: ASTCore, catalog: Catalog, parent: HostClass): ScopeChain = {

    PuppetScope.clear ()

    val toplevel_scope = PuppetScope.createNamedScope ("")
    val env = (new ScopeChain ()).addScope (toplevel_scope)

    val facter_env = Cmd.exec ("facter").get
 
    facter_env.lines.foreach ({ case line => {
        val kv = line.split ("=>").map (_.trim)
        if (kv.length > 1 // TODO : Hack to get past the failing smoke test for now
) env.setvar (kv(0), StringV (kv(1)))       }
    })
    
    eval (block, env, catalog, parent)
    env
  }


  def compile (ast: BlockStmtC): Either[List[(String, Catalog)], Catalog] = {

    /* TODO : Handle Staging in puppet
     * Add main to catalog
     * catalog.addResource (Resource ("stage", 'main, topscope)
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

        val main_resource = HostClass ('main.toString/*, Map[String, Value] ()*/)
        // catalog.addResource (main_resource) TODO

        val env = evalToplevel (ast, catalog, main_resource)
        val nodename = (eval (node.hostname, env, catalog, main_resource)).toPString

        // TODO: Bad Type coercion
        evalNode (nodename, node.stmts.asInstanceOf[BlockStmtC], env, catalog, main_resource)

        evalClasses ()
        evalDefinitions ()
        evalOverrides (catalog)
        (nodename, catalog)
      }}))
    }
    else
    {
      val catalog = new Catalog ()

      val main_resource = HostClass ('main.toString/*, Map[String, Value] ()*/)
      // catalog.addResource (main_resource) TODO

      val env = evalToplevel (ast, catalog, main_resource)
      // evalClasses ()
      evalOverrides (catalog)
      /*
      TODO 
      catalog.evalDefinitions (catalog)
      */

      Right (catalog)
    }
  }

  def evalOverrides (catalog: Catalog): Catalog = {
    catalog.overrides.foreach ({ case (ref, attrs) => 
      catalog.findResourcesFromRef (ref).foreach ({ case res =>
        attrs.foreach ({ case (k, v) => res.mergeAttr (k, v) })
      })
    })
    catalog
  }

  def evalClasses () {
    throw new Exception ("feature not supported yet")
  }

  def evalDefinitions () {
    throw new Exception ("feature not supported yet")
  }
}
