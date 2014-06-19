package puppet.core.eval

import puppet.core._
import puppet.syntax._
import puppet.util._

import scala.collection._
import scala.util.matching.Regex
import scala.util.Try

sealed abstract class Node (title: String)

// TODO : Add staging support
case class Resource (title: String, 
                     params: mutable.Map[String, Value]) extends Node (title) {

  private def depsToResRefs(v: Value): List[ResourceRefV] = v match {
    case v: ASTArrayV => v.value.toList flatMap depsToResRefs
    case v: ResourceRefV => List(v)
    case _ => throw new Exception("Value is not a valid resource reference")
  }

  private def attrToResRefs(key: String): List[ResourceRefV] =
    (params.get(key) map depsToResRefs) getOrElse List ()

  def sources: List[ResourceRefV] = attrToResRefs("require"):::attrToResRefs("subscribe")
  def targets: List[ResourceRefV] = attrToResRefs("before"):::attrToResRefs ("notify")

  def mergeAttr (name: String, value: Value, append: Boolean = false) {
    if (append)
      throw new Exception ("Append not supported yet")

    params += (name -> value)
  }
  
  def getAttr (name: String): Option[Value] = params get name

  def toResourceRefV: ResourceRefV =
    ResourceRefV (ResourceRefV(StringV("type"), params ("type"), FEqOp),
                  ResourceRefV(StringV("title"), params ("title"), FEqOp), FAndOp)
}

case class HostClass (title: String) extends Node (title) {}
case class Stage (title: String) extends Node (title) {}

object PuppetCompile {

  private val knownResourceTypes = List ("Augeas", "Computer", "Cron", "Exec",
    "File", "Filebucket", "Group", "Host", "Interface", "K5login",
    "Macauthorization", "Mailalias", "Maillist", "Mcx", "Mount",
    "Nagios_command", "Nagios_contact", "Nagios_contactgroup", "Nagios_host",
    "Nagios_hostdependency", "Nagios_hostescalation", "Nagios_hostextinfo",
    "Nagios_hostgroup", "Nagios_service", "Nagios_servicedependency",
    "Nagios_serviceescalation", "Nagios_serviceextinfo", "Nagios_servicegroup",
    "Nagios_timeperiod", "Notify", "Package", "Resources", "Router", "Schedule",
    "Scheduled_task", "Setboolean", "Selmodule", "Service", "Ssh_authorized_key",
    "Sshkey", "Stage", "Tidy", "User", "Vlan", "Yumrepo", "Zfs", "Zone", "Zpool")

  def evalResourceRef (ref: ResourceRefV)
                      (implicit resource: Resource): Boolean = ref.op match {
    case FEqOp    => resource.params get ref.lhs.toPString map(_ == ref.rhs) getOrElse false
    case FNotEqOp => resource.params get ref.lhs.toPString map(_ != ref.rhs) getOrElse false
    case FAndOp   => evalResourceRef(ref.lhs.asInstanceOf[ResourceRefV]) &&
                     evalResourceRef(ref.rhs.asInstanceOf[ResourceRefV])
    case FOrOp    => evalResourceRef(ref.lhs.asInstanceOf[ResourceRefV]) ||
                     evalResourceRef(ref.rhs.asInstanceOf[ResourceRefV])
  }

  /*
   * All integer related operations have to follow ruby semantics and its flexibility/limitations
   *
   * Being ruby compliant, when we ask for left shift by a negative
   * number, ruby does a right shift by its absolute value.
   * Vice Versa for right shift
   */
  private def evalOp (op: BinOp, x: Value, y: Value): Value = op match {
    case Or          => BoolV(x.toBool || y.toBool)
    case And         => BoolV(x.toBool && y.toBool)
    case GreaterThan => BoolV(x.toDouble >  y.toDouble)
    case GreaterEq   => BoolV(x.toDouble >= y.toDouble)
    case LessThan    => BoolV(x.toDouble <  y.toDouble)
    case LessEq      => BoolV(x.toDouble <= y.toDouble)
    case NotEqual    => BoolV(! x.isEqual(y))
    case Equal       => BoolV(  x.isEqual(y))

    case LShift => StringV((if(y.toInt > 0) x.toInt << y.toInt else x.toInt >> y.toInt).toString)
    case RShift => StringV((if(y.toInt > 0) x.toInt >> y.toInt else x.toInt << y.toInt).toString)

    case Plus  => StringV(Try(x.toInt + y.toInt).map(_.toString) getOrElse (x.toDouble + y.toDouble).toString)
    case Minus => StringV(Try(x.toInt - y.toInt).map(_.toString) getOrElse (x.toDouble - y.toDouble).toString)
    case Div   => StringV(Try(x.toInt / y.toInt).map(_.toString) getOrElse (x.toDouble / y.toDouble).toString)
    case Mult  => StringV(Try(x.toInt * y.toInt).map(_.toString) getOrElse (x.toDouble * y.toDouble).toString)

    case Mod   => StringV((x.toInt % y.toInt).toString)

    // Regex related match, string is left operand and regular expression as right operand, returns a boolean
    case Match   => BoolV(!(y.asInstanceOf[RegexV].value findFirstIn x.toPString).isEmpty)
    case NoMatch => BoolV( (y.asInstanceOf[RegexV].value findFirstIn x.toPString).isEmpty) // XXX : Should have been desugared

    case In      => BoolV(y match {
      case StringV  (v) => v contains x.asInstanceOf[StringV].value
      case ASTArrayV(v) => v contains x.asInstanceOf[StringV]
      case ASTHashV (v) => v contains x.asInstanceOf[StringV].value
      case _ => throw new Exception("\"In\" Operator not supported for types other than String, Array or Hash")
    })
  }

  // TODO: interpolate!!
  private def interpolate (str: String, env: ScopeChain): String = {
    str
  }

  private def stripQuote(str: String) =
    if (str(0) == '\'' || str(0) == '\"')
      str.stripPrefix(str(0).toString).stripSuffix(str(0).toString)
    else str

  // TODO : Redundant with a function in Resource class
  private def resourceASTToTitle (attrs: ASTHashV): String =
    attrs.value("type").toPString + ":" + attrs.value("title").toPString

  // TODO : More precise type than 'Value'
  private def eval(ast: ASTCore)
                  (implicit  env: ScopeChain, catalog: Catalog, parent: HostClass): Value = ast match {
    case UndefC     => UndefV
    case BoolC(b)   => BoolV(b)
    case StringC(s) => StringV(stripQuote(interpolate(s, env)))
    case TypeC(t)   => StringV(t) // XXX: Not sure
    case NameC(n)   => StringV(n) // XXX: Not sure
    case RegexC(r)  => RegexV(new Regex(r))
    case ASTHashC(kvs) => ASTHashV(kvs.map({ case (k, v) => (eval(k).asInstanceOf[StringV].value, eval(v))}).toMap)
    case ASTArrayC(arr) => ASTArrayV(arr.map(eval _).toArray) // TODO : Should have been toArray from beginning

    case HashOrArrayAccessC(variable, keys) =>
      keys.map(eval(_)).foldLeft(eval(variable))({ case(ASTHashV(h), key) => h(key.asInstanceOf[StringV].value)
                                                   case(ASTArrayV(a), key) => a(key.asInstanceOf[StringV].value.toInt)
                                                   case(_, _) => throw new Exception("Array or Hash expected") })

    case VariableC(value) => env.getvar(value) getOrElse UndefV

    case BlockStmtC(exprs) => {
      val scope = PuppetScope.createEphemeralScope ()
      val new_env = env.addScope (scope)
      // Return the last evaluated value
      exprs.map (eval(_)(new_env, catalog, parent)).head
      // XXX: Maybe destroy newly created ephemeral scope
    }

    case IfElseC (test, true_br, false_br) =>
      eval(if(eval(test).toBool) true_br else false_br)

    case BinExprC (lhs, rhs, op) => evalOp(op, eval(lhs), eval(rhs))
    case NotExprC(oper) => BoolV(!eval(oper).toBool)
    case FuncAppC(name, args) => Function(eval(name).toPString, catalog, parent, args.map (eval _).toSeq:_*)

    // TODO : I dont think that Import should have reached this far, it should have been eliminated earlier
    case ImportC(imports) => throw new Exception ("Feature not supported yet")

    case VardefC(variable, value, append) => {
      val puppet_value = eval(value)
      env.setvar(variable.asInstanceOf[VariableC].value, puppet_value, append)
      puppet_value
    }

    case OrderResourceC (source, target, refresh) => {
      val lhs = eval(source).asInstanceOf[ResourceRefV]
      val rhs = eval(target).asInstanceOf[ResourceRefV]
      catalog.addRelationship (lhs, rhs, refresh)
      rhs
    }

    case AttributeC(name, value, is_append) =>
      if (is_append) throw new Exception ("Appending of attributes is not supported yet")
      else  ASTHashV(immutable.Map(eval(name).asInstanceOf[StringV].toPString -> eval(value)))

    case ResourceDeclC(attrs) => {
      val params = attrs.map(eval(_)).map(_.asInstanceOf[ASTHashV]).reduce(_.append (_))

      // Check for class or defined or resource as they share the same format
      if (params.value("type").toPString == "Class") {
        val name = params.value ("title").toPString
        // Its a class, schedule it for evaluation
        catalog.addClass (name, params.value.toList)
        UndefV
      }
      else if (knownResourceTypes.contains (params.value("type").toPString)) {
        val resource = Resource (resourceASTToTitle (params), mutable.Map (params.value.toSeq:_*))
        val resourceref = resource.toResourceRefV

        // TODO: either of source or targets could be a class (which may or maynot need declaration)
        resource.sources.foreach (catalog.addRelationship (_, resourceref))
        resource.targets.foreach (catalog.addRelationship (resourceref, _))
        catalog.addResource (resource, parent)

        resourceref
      }
      else { // Most likely its a defined type, treat it as such
        val name = params.value ("type").toPString
        val title = params.value ("title").toPString
        catalog.addDefinition(name, ("name", StringV(title))::params.value.toList)
        UndefV // TODO : May be return a resource ref
      }
    }

    case FilterExprC(lhs, rhs, op) => ResourceRefV(eval(lhs), eval(rhs), op)

    case ResourceOverrideC (ref, attrs) => {
      val refv = eval(ref)
      val params = (attrs map (eval(_)) map(_.asInstanceOf[ASTHashV]) reduce(_.append (_)))
      catalog.addOverride (refv.asInstanceOf[ResourceRefV], params.value)
      UndefV // XXX: return value, dont know what to return
    }
 
    // TODO : Partial function
    case _ => UndefV
  }

  def evalNode (name: String, block: ASTCore, env: ScopeChain, catalog: Catalog, parent: HostClass) {
    // Setup node scope and evaluate
    val node_scope = PuppetScope.createNamedScope (name)
    eval (block)(env.addScope(node_scope), catalog, parent)
  }

  def evalToplevel (block: ASTCore, catalog: Catalog, parent: HostClass): ScopeChain = {

    PuppetScope.clear() // XXX: Imperative

    val toplevel = PuppetScope.createNamedScope("")
    val env = (new ScopeChain ()).addScope(toplevel)

    val facter_env = Cmd.exec("facter").get
 
    facter_env.lines.foreach({ case line => {
        val kv = line.split ("=>").map (_.trim)
        if (kv.length > 1 // TODO : Hack to get past the failing smoke test for now
) env.setvar (kv(0), StringV (kv(1)))       }
    })
    
    block.asInstanceOf[BlockStmtC].exprs.foreach(eval(_)(env, catalog, parent))
    env
  }

  def compile(ast: BlockStmtC): Either[List[(String, Catalog)], Catalog] = {

    /* TODO : Handle Staging in puppet
     * Add main to catalog
     * catalog.addResource (Resource ("stage", 'main, topscope)
     */

    // Not sure if this is required
    TypeCollection.add (HostclassC ('main.toString, List (), None, ast))

    def f (s: ASTCore): Unit = s match {
      case hc:   HostclassC  => TypeCollection.add (hc); hc.stmts.asInstanceOf[BlockStmtC].exprs.foreach (f)
      case defn: DefinitionC => TypeCollection.add (defn)
      case _ => ()
    }
    ast.exprs.foreach (f)

    // Filtering + Type extraction via partial function
    val nodes = ast.exprs.collect ({ case node: NodeC => node })
    if (nodes.exists (!_.parent.isEmpty))
      throw new Exception ("Node inheritance not supported, deprecated by Puppet")

    // Wrap in original hostclass for main
    if (nodes.length > 0) {
      Left (nodes.map ((node => {
        val catalog = new Catalog ()

        val main_resource = HostClass('main.toString/*, Map[String, Value] ()*/)
        catalog.addHostClass(main_resource)

        val env = evalToplevel(ast, catalog, main_resource)
        val nodename = (eval(node.hostname)(env, catalog, main_resource)).toPString

        evalNode (nodename, node.stmts.asInstanceOf[BlockStmtC], env, catalog, main_resource)

        evalDefinitions (catalog, main_resource)
        evalClasses (catalog, main_resource)
        evalOverrides (catalog)
        (nodename, catalog)
      })))
    }
    else
    {
      val catalog = new Catalog ()

      val main_resource = HostClass ('main.toString/*, Map[String, Value] ()*/)
      catalog.addHostClass (main_resource)

      val env = evalToplevel (ast, catalog, main_resource)
      evalDefinitions (catalog, main_resource)
      evalClasses (catalog, main_resource)
      evalOverrides (catalog)
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

  /*
   * This is a simplified class evaluator
   *
   * Things that are being omitted or assumed are already deprecated
   * or in the process of deprecation by puppet
   *
   * Nested classes are not supported. They don't have access to variables in
   * outer class's lexical scope, neither are they included when the outer
   * class is included in a manifest. The outer class just serves as a namespace
   * for the inner class. The inner class cannot be directly referenced without
   * scoping it with its outer class name. This feature is not officially
   * deprecated by puppet yet but official puppet-lint tools marks it as a warning
   *
   * Node scope esp. for classes is something caught in between transitioning
   * from dynamic scoping in puppet < 2.7 to lexical scoping in puppet >= 2.7.
   * 
   * $toplevel_variable = "toplevel"
   * class foo { notice ("$node_variable") }
   *
   * node bar.baz.com { 
   *   $node_variable = "this is bar.baz.com"
   *
   * case $::os {
   *   'fedora': { $local = "this is fedora running on node $node_variable"
   *               include foo }
   *   'ubuntu': { $local = "this is ubuntu running on node $node_variable"
   *               include foo }
   * }
   * 
   * In the above example, due to mixing lexical and dynamic scoping, the variable
   * "$node_variable" is available to class but "$local" variable is not
   *
   * No nested classes + no node level dynamic scoping implies a class evaluation
   * always gets toplevel (global) scope and its parent class scope
   *
   * node level variables again are warned by puppet-lint tool.
   */

  // We don't have nested class support yet
  private def fillParamsInScope (env: ScopeChain,
                                 // args are what a construct declares (defaults etc in argment lists)
                                 args: List[(String, Option[Value])],
                                 // Params are what is provided to a construct
                                 params: List[(String, Value)]) {
    val envVars = args.unzip._1.toSet union params.unzip._1.toSet
    envVars.foreach((arg) => env.setvar(arg, ((params.toMap) get arg) getOrElse
                                             (((args.toMap) apply arg) getOrElse 
                                              (throw new Exception("No value available for variable '%s'".format(arg))))))
  }

  private def evalClass (catalog: Catalog,
                         hostclass: HostclassC,
                         params: List [(String, Value)],
                         dparent: HostClass): Catalog = {
    var env = (new ScopeChain ()).addScope ("") // Add toplevel scope
    val name = hostclass.classname

    // get toplevel scope
    if (!hostclass.parent.isEmpty) {
      
      val parent = hostclass.parent.get
      val parentclass = (TypeCollection.getClass (parent)) getOrElse (throw new Exception ("Parent class not found"))

      // Arguments are strictly not allowed for parent class 
      if (parentclass.args.length > 0)
        throw new Exception ("Parent class is not supposed to have arguments")

      evalClass (catalog, parentclass, List () /* no params for parent class */, dparent)
      env = env.addScope (parent)
    }

    val args = hostclass.args.map ({ case (variable, oval) => (variable.value, oval.map (eval (_)(env, catalog, dparent))) })

    env = env.addScope (PuppetScope.createNamedScope (name))

    fillParamsInScope(env, args, params)
    
    catalog.addHostClass(HostClass(name))
    hostclass.stmts.asInstanceOf[BlockStmtC].exprs.foreach(eval(_)(env, catalog, HostClass(name)))
    catalog
  }

  def evalClasses(catalog: Catalog, parent: HostClass): Catalog = {
    // Evaluating a class can generate more classes
    catalog.classes.foreach({ case klass => 
      evalClass (catalog,
                 TypeCollection.getClass (klass._1) getOrElse 
                   (throw new Exception("\"%s\" class not found in catalog".format(klass._1))),
                 klass._2, parent) 
    })
    catalog
  }

  private def evalDefinition (catalog: Catalog,
                              definition: DefinitionC,
                              params: List[(String, Value)],
                              dparent: HostClass): Catalog = {

    var env = (new ScopeChain()).addScope("") // Add toplevel scope

    val args = definition.args.map({ case(variable, oval) => (variable.value, oval.map(eval(_)(env, catalog, dparent))) })
    val name = params.find(_._1 == "title").get._2.asInstanceOf[StringV].value
    env = env.addScope(PuppetScope.createNamedScope(name))
    fillParamsInScope(env, args, params)
    definition.stmts.asInstanceOf[BlockStmtC].exprs.foreach(eval(_)(env, catalog, dparent))
    catalog
  }

  // TODO : See parent
  def evalDefinitions (catalog: Catalog, parent: HostClass): Catalog = {
    catalog.defines.foreach({ case define =>
      evalDefinition (catalog, 
                      TypeCollection.getDefinition (define._1) getOrElse
                      (throw new Exception ("\"%s\" definition not found in catalog".format(define._1))),
                      define._2, parent)
    })
    catalog
  }
}
