package puppet.core.eval

import puppet.core._
import puppet.core.eval.{Attributes => Attrs}
import puppet.syntax._
import puppet.util._

import scala.collection._
import scala.collection.{mutable => mut}
import scala.util.matching.Regex
import scala.util.Try

object PuppetCompile {

  // TODO : CatalogElement should not be exposed directory but should be a trait
  def evalResourceRef (ref: ResourceRefV)
                      (implicit resource: CatalogElement): Boolean = ref.op match {
    case FEqOp    => resource.params get ref.lhs.toPString map(_ == ref.rhs) getOrElse false
    case FNotEqOp => resource.params get ref.lhs.toPString map(_ != ref.rhs) getOrElse false
    case FAndOp   => evalResourceRef(ref.lhs.asInstanceOf[ResourceRefV]) &&
                     evalResourceRef(ref.rhs.asInstanceOf[ResourceRefV])
    case FOrOp    => evalResourceRef(ref.lhs.asInstanceOf[ResourceRefV]) ||
                     evalResourceRef(ref.rhs.asInstanceOf[ResourceRefV])
  }

  /*
   * All integer related operations have to follow ruby semantics and its
   * flexibilities and limitations.
   *
   * Being ruby compliant, when we ask for left shift by a negative
   * number, ruby does a right shift by its absolute value.
   * Vice Versa for right shift
   */
  private def evalOp(op: BinOp, x: Value, y: Value): Value = op match {
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

  private def stripQuote(str: String) =
    if (str.length >= 2 && (str(0) == '\'' || str(0) == '\"'))
      str.stripPrefix(str(0).toString).stripSuffix(str(0).toString)
    else str

  // TODO : More precise type than 'Value'
  private def eval(ast: ASTCore)
                  (implicit  env: ScopeChain, catalog: Catalog, containedBy: Option[ResourceRefV]): Value = ast match {
    case UndefC     => UndefV
    case BoolC(b)   => BoolV(b)
    case StringC(s) => StringV(stripQuote(s))
    case ConcatC(pre, mid, post) => StringV(eval(pre).asInstanceOf[StringV].toPString +
                                            eval(mid).toPString +
                                            eval(post).asInstanceOf[StringV].toPString)
    case TypeC(t)   => StringV(t)
    case NameC(n)   => StringV(n)
    case RegexC(r)  => RegexV(new Regex(r))
    case ASTHashC(kvs) => ASTHashV(kvs.map({ case (k, v) => (eval(k).asInstanceOf[StringV].value, eval(v))}).toMap)
    case ASTArrayC(arr) => ASTArrayV(arr.map(eval _).toArray) // TODO : Should have been toArray from beginning

    case HashOrArrayAccessC(variable, keys) =>
      keys.map(eval(_)).foldLeft(eval(variable))({ case(ASTHashV(h), key) => h(key.asInstanceOf[StringV].value)
                                                   case(ASTArrayV(a), key) => a(key.asInstanceOf[StringV].value.toInt)
                                                   case(_, _) => throw new Exception("Array or Hash expected") })

    // XXX: getvar should be wrapeed in Try instead of having try in scopechain class
    case VariableC(value) => env.getvar(value) getOrElse UndefV

    // XXX: should we return head or the last element?
    case BlockStmtC(exprs) => exprs.map(eval(_)).head

    case IfElseC(test, true_br, false_br) =>
      eval(if(eval(test).toBool) true_br else false_br)

    case BinExprC(lhs, rhs, op) => evalOp(op, eval(lhs), eval(rhs))
    case NotExprC(oper) => BoolV(!eval(oper).toBool)
    case FuncAppC(name, args) => Function(eval(name).toPString, catalog, containedBy, args.map((a) => (eval(a), a)).toSeq:_*)

    // TODO : I dont think that Import should have reached this far, it should have been eliminated earlier
    case ImportC(imports) => throw new Exception("Feature not supported yet")

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
      if (is_append) throw new Exception ("Appending of attributes is not supported yet") // TODO
      else  ASTHashV(immutable.Map(eval(name).asInstanceOf[StringV].toPString -> eval(value)))

    case ResourceDeclC(attrs) => {
      val params = attrs.map(eval(_)).map(_.asInstanceOf[ASTHashV]).reduce(_.append(_))
      catalog.addResource(mut.Map(params.value.toSeq: _*), containedBy)
    }

    case FilterExprC(lhs, rhs, op) => ResourceRefV(eval(lhs), eval(rhs), op)

    case ResourceOverrideC (ref, attrs) => {
      val refv = eval(ref)
      val params = (attrs map (eval(_)) map(_.asInstanceOf[ASTHashV]) reduce(_.append (_)))
      catalog.addOverride (refv.asInstanceOf[ResourceRefV], mut.Map(params.value.toSeq: _*))
      UndefV // XXX: return value, dont know what to return
    }

    // TODO : Partial function
    case _ => UndefV
  }

/*
  def evalNode (name: String, block: ASTCore, env: ScopeChain, catalog: Catalog, containedBy: String) {
    // Setup node scope and evaluate
    val node_scope = PuppetScope.createNamedScope (name)
    eval (block)(env.addScope(node_scope), catalog, containedBy)
  }

  def evalToplevel (block: ASTCore, catalog: Catalog, containedBy: String): ScopeChain = {

    PuppetScope.clear() // XXX: Imperative

    val toplevel = PuppetScope.createNamedScope("")
    val env = (new ScopeChain ()).addScope(toplevel)

    val facter_env = Cmd.exec("facter").get

    facter_env.lines.foreach({ case line => {
        val kv = line.split ("=>").map (_.trim)
        if (kv.length > 1 // TODO : Hack to get past the failing smoke test for now
) env.setvar (kv(0), StringV (kv(1)))       }
    })

    block.asInstanceOf[BlockStmtC].exprs.foreach(eval(_)(env, catalog, containedBy))
    env
  }
  */

  def setupEnv () {
    PuppetScope.clear() // XXX: Imperative

    val toplevel = PuppetScope.createNamedScope("")
    val env = (new ScopeChain ()).addScope(toplevel)

    val facter_env = Cmd.exec("facter").get

    facter_env.lines.foreach({ case line => {
        val kv = line.split ("=>").map (_.trim)
        if (kv.length > 1 // TODO : Hack to get past the failing smoke test for now
) env.setvar (kv(0), StringV (kv(1)))       }
    })
  }

  def compile(ast: BlockStmtC): Either[List[(String, Catalog)], Catalog] = {

    /* TODO : Handle Staging in puppet */

    TypeCollection.clear()
    TypeCollection.add(HostclassC('main.toString, List (), None, ast))

    def process(s: ASTCore): Unit = s match {
      case hc:   HostclassC  => TypeCollection.add (hc); hc.stmts.asInstanceOf[BlockStmtC].exprs.foreach(process)
      case defn: DefinitionC => TypeCollection.add (defn)
      case _ => ()
    }
    ast.exprs.foreach(process)

    setupEnv()

    /*
    // Filtering + Type extraction via partial function
    val nodes = ast.exprs.collect ({ case node: NodeC => node })
    if (nodes.exists (!_.parent.isEmpty))
      throw new Exception ("Node inheritance not supported, deprecated by Puppet")

    // Wrap in original hostclass for main
    if (nodes.length > 0) {
      Left (nodes.map ((node => {
        implicit val catalog = new Catalog ()

        val mainClass = mut.Map("title" -> StringV('main.toString),
                                "type" -> StringV("Class"))
        catalog.addResource(mainClass)

        val nodename = (eval(node.hostname)(env, catalog, 'main.toString)).toPString

        evalNode (nodename, node.stmts.asInstanceOf[BlockStmtC], env, catalog, 'main.toString)

        var classes = List[(String, List[(String, Value)], String)]()
        var defines = List[(String, List[(String, Value)], String)]()
        var klass  = catalog.getNextClass()
        var define = catalog.getNextDefinition()
        while (!klass.isEmpty && !define.isEmpty) {
          klass.map(evalClass(_))
          define.map(evalDefine(_))
        }

        // TODO: Collections
        evalOverrides (catalog)

        // Process relationships, all we have left are resources after converging
        catalog.resources.foreach ({(r) => r.sources.foreach(catalog.addRelationship(_, r.toResourceRefV));
                                           r.targets.foreach(catalog.addRelationship(r.toResourceRefV, _)) })

        (nodename, catalog)
      })))
    }
    else
    */
    {
      implicit val catalog = new Catalog ()

      val mainClass = Attrs.resourceBasicAttributes("Class", 'main.toString)
      catalog.addResource(mainClass)

      def converge(): Unit = {
        val klass = catalog.getNextClass()
        // TODO: Collections
        val define = catalog.getNextDefinition()
        if (!klass.isEmpty || !define.isEmpty) {
          klass.map(evalClass(_))
          define.map(evalDefinition(_))
          converge()
        }
      }

      converge()

      evalOverrides(catalog)

      // Process relationships, all we have left are resources after converging
      catalog.resources.foreach ({(r) => r.sources.foreach(catalog.addRelationship(_, r.toResourceRefV));
                                         r.targets.foreach(catalog.addRelationship(r.toResourceRefV, _))})

      Right (catalog)
    }
  }

  // TODO : Test
  // TODO : Only new attributes can be assigned a value, already existing attributes have to be appended
  //        otherwise the manifest is not supposed to compile
  def evalOverrides(catalog: Catalog): Catalog = {
    catalog.overrides.foreach({ case (ref, attrs) =>
      catalog.find(ref).foreach((res) => attrs.foreach({ case (k, v) => res.mergeAttr(k, v) }))
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

  private def mergeParamAndArgs(// args are what a construct declares (defaults etc in argment lists)
                                args:List[(String, Option[Value])],
                                // Params are what is provided to a construct
                                params: List[(String, Value)]): List[(String, Value)] =
    (args.unzip._1 ++ params.unzip._1).distinct
    .map((arg) => (arg, ((params.toMap) get arg) getOrElse // Choose provided value over defaults
                        (((args.toMap) apply arg) getOrElse  // Look for default in case no value is provided
                        (throw new Exception("No value available for variable '%s'".format(arg))))))

  private def evalClass(klass: HostClass)
                       (implicit catalog: Catalog) {

    val klassAST = TypeCollection.getClass(klass.name) getOrElse
                   (throw new Exception("Puppet class %s not found".format(klass.name)))
    implicit var env = (new ScopeChain ()).addScope ("") // Add toplevel scope
    implicit val container = Some(klass.toResourceRefV) // resources withing this class are contained by it

    // Eval parent if present
    if (!klassAST.parent.isEmpty) {
      // We need to strip prefix because
      val parent = klassAST.parent.get.stripPrefix("::")
      val parentclass = (TypeCollection.getClass(parent)) getOrElse
                        (throw new Exception(s"class $parent not found"))

      // Arguments are strictly not allowed for parent class
      if (parentclass.args.length > 0)
        throw new Exception ("Parent class is not supposed to have arguments")

      /* Check if scope by the classname already exists, if it does then the parent class has already
       * been evaluated. Skip evaluation and merge in the scope.
       */
       if(!PuppetScope.scope_exists(parent)) {

         catalog.addResource(Attrs.resourceBasicAttributes("Class", parent))
         // Immediately consume; Not thread safe
         evalClass(catalog.getNextClass().get)
       }

      env = env.addScope(parent)
    }

    val args = klassAST.args.map({case (variable, oVal) => (variable.value, oVal.map(eval(_))) })
    // 'main class is a dummy class that bounds toplevel statement and needs to be handled as special case
    if (klass.name != 'main.toString) env = env.addScope(PuppetScope.createNamedScope(klass.name))
    mergeParamAndArgs(args, klass.params.toList).foreach({case (k, v) => env.setvar(k, v)})

    klassAST.stmts.asInstanceOf[BlockStmtC].exprs.foreach(eval(_))
  }

  private def evalDefinition(define: Definition)
                            (implicit catalog: Catalog) {

    implicit var env = (new ScopeChain()).addScope("") // Add toplevel scope
    implicit val container = Some(define.toResourceRefV) // resources within this definition are contained by it
    val defineAST = TypeCollection.getDefinition(define.typ) getOrElse
                      (throw new Exception ("\"%s\" definition not found in catalog".format(define.typ)))

    val args = defineAST.args.map({ case(variable, oval) => (variable.value, oval.map(eval(_))) })
    env = env.addScope(PuppetScope.createNamedScope(define.name))
    mergeParamAndArgs(args, define.params.toList).foreach({case (k, v) => env.setvar(k, v)})

    defineAST.stmts.asInstanceOf[BlockStmtC].exprs.foreach(eval(_))
  }
}
