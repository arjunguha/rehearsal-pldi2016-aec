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


  private def interpolate (str: String, env: ScopeChain): String = {
    // TODO: interpolate!!
    str
  }

  private def resourceASTToTitle (attrs: ASTHashV): String = {
    attrs.value ("type").toPString + ":" + attrs.value ("title").toPString
  }

  // TODO : Catalog is fixed, can be curried away
  // TODO : More precise type than 'Value'
  private def eval (ast: ASTCore, env: ScopeChain, catalog: Catalog): Value = ast match {

    case UndefC          => UndefV
    case BoolC (value)   => BoolV (value)
    case StringC (value) => StringV (interpolate (value, env))
    case TypeC (value)   => StringV (value) // XXX: Not sure
    case NameC (value)   => StringV (value) // XXX: Not sure
    case RegexC (value)  => RegexV (new Regex (value))
    case ASTHashC (kvs)  => ASTHashV (kvs.map ({ case (k, v) => (eval (k, env, catalog).asInstanceOf[StringV].value,
                                                                 eval (v, env, catalog))}).toMap)
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
      if ((eval (test, env, catalog)).toBool) eval (true_br, env, catalog)
      else eval (false_br, env, catalog)
    }

    case BinExprC (lhs, rhs, op) => eval_op (op, eval (lhs, env, catalog), eval (rhs, env, catalog))
    case NotExprC (oper) => BoolV (!(eval (oper, env, catalog)).toBool)
    case FuncAppC (name, args) => Function ((eval (name, env, catalog)).toPString,  args.map (eval (_, env, catalog)).toSeq:_*)

    // TODO : I dont think that Import should have reached this far, it should have been eliminated earlier
    case ImportC (imports) => throw new Exception ("Feature not supported yet")

    case VardefC (variable, value, append) => {
      val puppet_value = eval (value, env, catalog)
      env.setvar (variable.asInstanceOf[VariableC].value, puppet_value, append)
      puppet_value
    }

    case OrderResourceC (source, target, refresh) => {
      val lhs = eval (source, env, catalog).asInstanceOf[ResourceRefV]
      val rhs = eval (target, env, catalog).asInstanceOf[ResourceRefV]
      catalog.addRelationship (lhs, rhs, refresh)
      rhs
    }

    case AttributeC (name, value, is_append) =>
      if (is_append) throw new Exception ("Appending of attributes is not supported yet")
      else  ASTHashV (immutable.Map ((eval (name, env, catalog)).asInstanceOf[StringV].toPString -> eval (value, env, catalog)))

    case ResourceDeclC (attrs) => {
      val params = attrs.map (eval (_, env, catalog)) map (_.asInstanceOf[ASTHashV]) reduce (_.append (_))
      val resource = Resource (resourceASTToTitle (params), mutable.Map (params.value.toSeq:_*))
      val resourceref = resource.toResourceRefV

      resource.sources.foreach (catalog.addRelationship (_, resourceref))
      resource.targets.foreach (catalog.addRelationship (resourceref, _))
      catalog.addResource (resource)

      resourceref
    }

    case FilterExprC (lhs, rhs, op) => op match {
      case FEqOp    => ResourceRefV (eval (lhs, env, catalog), eval (rhs, env, catalog), FEqOp)
      case FNotEqOp => ResourceRefV (eval (lhs, env, catalog), eval (rhs, env, catalog), FNotEqOp)
      case FAndOp   => ResourceRefV (eval (lhs, env, catalog), eval (rhs, env, catalog), FAndOp)
      case FOrOp    => ResourceRefV (eval (lhs, env, catalog), eval (rhs, env, catalog), FOrOp)
    }

    case ResourceOverrideC (ref, attrs) => { 
      val refv = eval (ref, env, catalog)
      val params = (attrs map (eval (_, env, catalog)) map (_.asInstanceOf[ASTHashV]) reduce (_.append (_)))
      catalog.addOverride (refv.asInstanceOf[ResourceRefV], params.value)
      UndefV // return value, dont know what to return
    }

    // TODO : Bad, convert into partial function
    case _ => UndefV
  }


  def evalNode (name: String, ast: BlockStmtC, env: ScopeChain, catalog: Catalog) {

    // Setup node scope
    val node_scope = PuppetScope.createNamedScope (name)
    val env_new = env.addScope (node_scope)

    ast.exprs.foreach (eval (_, env_new, catalog))
  }

  def evalToplevel (ast: BlockStmtC, catalog: Catalog): ScopeChain = {

    PuppetScope.clear ()

    val toplevel_scope = PuppetScope.createNamedScope ("")
    val env = (new ScopeChain ()).addScope (toplevel_scope)

    val facter_env = Cmd.exec ("facter").get
 
    facter_env.lines.foreach ({ case line => {
        val kv = line.split ("=>").map (_.trim)
        if (kv.length > 1 // TODO : Hack to get past the failing smoke test for now
) env.setvar (kv(0), StringV (kv(1)))       }
    })
  
    val main_resource = HostClass ('main.toString/*, Map[String, Value] ()*/)
    // catalog.addResource (main_resource) TODO
    
    ast.exprs.foreach (eval (_, env, catalog))
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
        val env = evalToplevel (ast, catalog)
        val nodename = (eval (node.hostname, env, catalog)).toPString

        // TODO: Bad Type coercion
        evalNode (nodename, node.stmts.asInstanceOf[BlockStmtC], env, catalog)

        evalClasses ()
        evalDefinitions ()
        evalOverrides (catalog)
        (nodename, catalog)
      }}))
    }
    else
    {
      val catalog = new Catalog ()
      val env = evalToplevel (ast, catalog)
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
