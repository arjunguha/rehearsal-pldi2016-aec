package rehearsal

object PuppetEval2 {

  import PuppetSyntax2._
  import scalax.collection.Graph
  import scalax.collection.Graph._
  import scalax.collection.GraphPredef._
  import scalax.collection.GraphEdge._
  import scalax.collection.edge.Implicits._
  import scala.util.parsing.combinator._

  object StringInterpolator {
    val parser = new PuppetParser2()
    import parser._

    def interpolate(env: Env, str: String): Expr = {
      val strs = str.split("""\$""")
      Str(strs(0) + strs.toList.drop(1).map(helper(env)).mkString(""))
    }

    def helper(env: Env)(str: String): String = {
      val tokens = str.split("""\s+""").toList
      checkBraces(env, tokens(0)) + tokens.drop(1).mkString("")
    }

    def checkBraces(env: Env, str: String): String = {
      str.indexOf("{") match {
        case 0 => {
          val ix = str.indexOf("}")
          val expr = str.substring(1, ix)
          val rest = str.substring(ix+1, str.length)
          evaluate(env, expr) + rest
        }
        case _ => evaluate(env, str)
      }
    }

    def evaluate(env: Env, str: String): String = {
      val strPrime = if(str.charAt(0) != '$') "$" + str else str
      parseAll(expr, strPrime) match {
        case Success(expr, _) => evalExpr(env, expr) match {
          case Str(s) => s
          case _ => throw EvalError(s"None string expression evaluated during string interpolation: $expr")
        }
        case m => throw EvalError(s"Could not parse interpolated expression: $m")
      }
    }

  }

  val primTypes =  Set("file", "package", "user", "group", "service",
                       "ssh_authorized_key", "augeas")

  case class VClass(name: String, env: Env,
                    args: Map[String, Option[Expr]], body: Manifest)

  case class VDefinedType(
    name: String,
    env: Env,
    args: Map[String, Option[Expr]],
    body: Manifest)

  type Env = Map[String, Expr]


  case class State(resources: Map[Node, ResourceVal],
                   deps: Graph[Node, DiEdge],
                   env: Env,
                   definedTypes: Map[String, VDefinedType],
                   classes: Map[String, VClass],
                   classGraph: Map[String, Graph[Node, DiEdge]],
                   stages: Map[String, Set[Node]])



  def evalAttrs(env: Env, attrs: Seq[Attribute]): Map[String, Expr] = {
    // TODO(arjun): duplicates are probably an error
    attrs.map({
      case Attribute(kExpr, v) => evalExpr(env, kExpr) match {
        case Str(k) => k -> evalExpr(env, v)
        case _ => throw EvalError("attribute key should be a string")
      }
    }).toMap
  }

  def evalTitle(env: Env, titleExpr: Expr): String = {
    evalExpr(env, titleExpr) match {
      case Str(title) => title
      case _ => throw EvalError("title should be a string")
    }
  }

  def resourceRefs(e: Expr): Seq[Node] = e match {
    case EResourceRef(typ, Str(title)) => Seq(Node(typ, title))
    case Array(seq) => seq.map(resourceRefs).flatten
    case _ => throw EvalError(s"expected resource reference, got $e ${e.pos}")
  }

  def extractRelationships(s: Node,
                           attrs: Map[String, Expr]): Graph[Node, DiEdge] = {

    def get(key: String) = resourceRefs(attrs.getOrElse(key, Array(Seq())))
    val before = get("before").map(r => DiEdge(s, r))
    val require = get("require").map(r => DiEdge(r, s))
    val notify = get("notify").map(r => DiEdge(s, r))
    val subscribe = get("subscribe").map(r => DiEdge(r, s))
    Graph.from(edges = Seq(before, require, notify, subscribe).flatten)
  }

  val relationshipParams = Seq("before", "require", "notify", "subscribe")

  // Produces a new state and a list of resource titles
  // TODO(arjun): Handle "require" and "before" dependencies.
  def evalResource(st: State, resource: Resource): (State, List[Node]) = {
    resource match {
      case ResourceRef(typ, titleExpr, Seq()) => {
        val node = Node(typ.toLowerCase, evalTitle(st.env, titleExpr))
        (st.copy(deps = st.deps + node), List(node))
      }
      case ResourceDecl(typ, lst) => {
        val (vals, relationships) = lst.map { case (titleExpr, attrs) =>
          val attrVals = evalAttrs(st.env, attrs)
          val resource = ResourceVal(typ, evalTitle(st.env, titleExpr),
                                     attrVals -- relationshipParams)
          val relationships = extractRelationships(resource.node, attrVals)
          (resource, relationships)
        }.unzip

        val newNodes: Set[Node] = vals.map(_.node).toSet
        //println(s"Creating nodes $nodes")
        val redefinedResources = st.resources.keySet.intersect(newNodes)
        if (redefinedResources.isEmpty == false) {
          throw EvalError(s"${redefinedResources.head} is already defined")
        }
        else {
          val newResources = vals.map(r => r.node -> r).toMap
          (st.copy(resources = st.resources ++ newResources,
                   deps = st.deps ++
                     Graph.from(newNodes, edges = Set()) ++
                     relationships.reduce(_ union _),
                   stages = newResources.foldRight(st.stages)(updateStage)),
           newNodes.toList)
        }
      }
    }
  }

  def evalEdges(st: State, lst: Seq[Resource]): (State, List[Node]) = lst match {
    case Seq() => (st, Nil)
    case r :: rest => {
      val (st1, titlesHd) = evalResource(st, r)
      val (st2, titlesTl) = evalEdges(st1, rest)
      val newDeps = for (x <- titlesHd; y <- titlesTl) yield { DiEdge(x, y) }
      (st2.copy(deps = st2.deps ++ newDeps), titlesHd)
    }
  }

  def matchCase(env: Env, v: Expr, aCase: Case): Boolean = aCase match {
    case CaseDefault(_) => true
    case CaseExpr(e, _) => evalExpr(env, e) == v
  }

  def evalManifest(st: State, manifest: Manifest): State = manifest match {
    case Empty => st
    case Block(m1, m2) => evalManifest(evalManifest(st, m1), m2)
    case EdgeList(lst) => evalEdges(st, lst)._1
    case Define(f, args, m) => {
      if (st.definedTypes.contains(f)) {
        throw EvalError(s"$f is already defined as a type")
      }
      else {
        // TODO(arjun): ensure no duplicate identifiers
        val vt = VDefinedType(f, st.env, args.map(a => a.id -> a.default).toMap,
                              m)
        st.copy(definedTypes = st.definedTypes + (f -> vt))
      }
    }
    case Class(f, args, _, m) => {
      if (st.classes.contains(f)) {
        throw EvalError(s"$f is already defined as a class")
      }
      else {
        // TODO(arjun): ensure no duplicate identifiers
        val vc = VClass(f, st.env,
                        args.map(a => a.id -> a.default).toMap,
                        m)
        st.copy(classes = st.classes + (f -> vc))
      }
    }
    case ESet(x, e) => {
      if (st.env.contains(x)) {
        throw EvalError(s"$x is already set")
      }
      else {
        st.copy(env = st.env + (x -> evalExpr(st.env, e)))
      }
    }
    case ITE(e, m1, m2) => evalBool(st.env, e) match {
      case true => evalManifest(st, m1)
      case false => evalManifest(st, m2)
    }
    case Include(title) => st.copy(deps = st.deps + Node("class", evalTitle(st.env, title)))
    case MApp("fail", Seq(str)) => evalExpr(st.env, str) match {
      // TODO(arjun): Different type of error
      case Str(str) => throw EvalError(s"user-defined failure: $str")
      case v => throw EvalError(s"expected string argument, got $v ${manifest.pos}")
    }
    case MApp(f, _) => throw NotImplemented("unsupported function: $f ${manifest.pos}")
    case MCase(e, cases) => {
      val v = evalExpr(st.env, e)
      cases.find(c => matchCase(st.env, v, c)) match {
        case None => st
        case Some(CaseDefault(m)) => evalManifest(st, m)
        case Some(CaseExpr(_, m)) => evalManifest(st, m)
      }
    }
  }

  // Helps implement conditionals. "Truthy" values are mapped to Scala's true
  // and "falsy" values are mapped to Scala's false.
  def evalBool(env: Env, expr: Expr): Boolean = evalExpr(env, expr) match {
    case Bool(true) => true
    case Bool(false) => false
    case Undef => false
    case v => throw EvalError(s"predicate evaluated to $v")
  }

  def evalExpr(env: Env, expr: Expr): Expr = expr match {
    case Undef => Undef
    case Num(n) => Num(n)
    case Str(str) => StringInterpolator.interpolate(env, str)
    case Bool(b) => Bool(b)
    case EResourceRef(typ, title) => EResourceRef(typ.toLowerCase, evalExpr(env, title))
    case Eq(e1, e2) => Bool(evalExpr(env, e1) == evalExpr(env, e2))
    case Not(e) => Bool(!evalBool(env, e))
    case Var(x) => env.get(x) match {
      case Some(v) => v
      // NOTE(arjun): Do not change this. Strictly speaking, this is not an
      // error. But, silently returning undef will make us miss other bugs in
      // our implementation. If a test manifest actually uses this feature,
      // modify it so that the undeclared variable is set to Undef.
      case None => throw EvalError(s"undefined variable: $x (${expr.pos})")
    }
    case Array(es) => Array(es.map(e => evalExpr(env, e)))
    case App("template", Seq(e)) => evalExpr(env, e) match {
      // TODO(arjun): This is bogus. It is supposed to use filename as a
      // template string. The file contents have patterns that refer to variables
      // in the environment.
      case Str(filename) => Str(filename)
      case _ => throw EvalError("template function expects a string argument")
    }
    case App(f, args) => throw NotImplemented(s"function $f (${expr.pos})")
    case Cond(e1, e2, e3) => evalBool(env, e1) match {
      case true => evalExpr(env, e2)
      case false => evalExpr(env, e3)
    }
    case _ => throw NotImplemented(expr.toString)
  }

  def splice[A](outer: Graph[A, DiEdge], node: A,
                inner: Graph[A, DiEdge]): Graph[A, DiEdge] = {
    val innerNode = outer.get(node)
    val toEdges = (for (from <- innerNode.diPredecessors;
                        to <- inner.nodes.filter(_.inDegree == 0))
                   yield (DiEdge(from.value, to.value)))
    val fromEdges = (for (from <- inner.nodes.filter(_.outDegree == 0);
                          to <- innerNode.diSuccessors)
                     yield (DiEdge(from.value, to.value)))
    outer ++ inner ++ fromEdges ++ toEdges - innerNode
  }

  def instantiateClass(st: State, classNode: Node): State = {
    require(classNode.typ == "class")
    val title = classNode.title
    st.classGraph.get(title) match {
      // Class has already been instantiated, splice it in where necesarry
      case Some(deps) =>
          st.copy(deps = splice(st.deps, st.deps.get(Node("class", title)), deps))
      case None => st.classes.get(title) match {
        case Some(VClass(_, classEnv, args, m)) => {
          assert(args.size == 0, "not implemented class args")
          val st1 = evalManifest(st.copy(deps = Graph.empty), m)
          st1.copy(deps = splice(st.deps, st.deps.get(Node("class", title)), st1.deps),
            classGraph = st1.classGraph + (title -> st1.deps)
          )
        }
        case None => throw EvalError(s"class not found: $title ${st.classes.keys}")
      }
    }
  }

  def instantiateType(st: State, node: Node): State = {
    val VDefinedType(_, env, formals, m) = st.definedTypes(node.typ)
    val ResourceVal(_, _, actuals) = st.resources(node)
    val unexpected = actuals.keySet -- actuals.keySet
    if (unexpected.isEmpty == false) {
      throw EvalError(s"unexpected arguments: ${unexpected}")
    }
    val titlePair = ("title" -> Str(node.title))
    val evaluated = formals.toList.map {
      case (x, None) => actuals.get(x) match {
        case Some(v) => (x, v)
        case None => throw EvalError(s"expected argument $x")
      }
      case (x, Some(default)) => actuals.get(x) match {
        case Some(v) => (x, v)
        // Notice that default expressions are evaluated in the lexical scope
        // of the type definition, but with $title bound dynamically.
        case None => (x, evalExpr(env + titlePair, default))
      }
    }.toMap
    val evaluatedPrime = evaluated.get("name") match {
      case None => evaluated + ("name" -> Str(node.title))
      case _ => evaluated
    }
    val st1 = evalManifest(st.copy(deps = Graph.empty,
                                   env = evaluatedPrime.toMap + titlePair),
                           m)
    st1.copy(deps = splice(st.deps, node, st1.deps),
             resources = st1.resources - node)
  }


  def evalLoop(st: State): State = {
    val st1 = st
    // Select newly instantiated classes and splice them into the graph
    val instClasses = st1.deps.nodes.filter(_.typ == "class").map(_.value)
    val st2 = instClasses.foldLeft(st1)(instantiateClass)
    // Select newly instantiated defined types and splice them into the graph
    val newInstances = st2.deps.nodes
      .filter(node => st2.definedTypes.contains(node.typ))
      .map(_.value)
    val st3 = newInstances.foldLeft(st2)(instantiateType)
    if (newInstances.isEmpty && instClasses.isEmpty) {
      st3 // st1 == st2 == st3
    }
    else {
      evalLoop(st3)
    }
  }

  val emptyState = State(
    resources = Map(),
    deps = Graph.empty,
    env = Map("title" -> Str("main"), "name" -> Str("main")),
    definedTypes = Map(),
    classes = Map(),
    classGraph = Map(),
    stages = Map())

  def updateStage(res: (Node, ResourceVal), stages: Map[String, Set[Node]]): Map[String, Set[Node]] = res match {
    case (node, ResourceVal(_, _, attrMap)) =>
      attrMap.get("stage") match {
        case Some(Str(stage)) => addStage(stage, node, stages)
        case Some(stage) => throw EvalError(s"Stage evaluated to non-string. $stage")
        case None => addStage("main", node, stages)
      }
  }

  def addStage(stage: String, node: Node, stages: Map[String, Set[Node]]): Map[String, Set[Node]] =
      stages.get(stage) match {
        case None => stages + (stage -> Set(node))
        case Some(set) => stages + (stage -> (set + node))
      }

  def stageExpansion(st: State): State = {
    val st1 = st
    val instStages = st1.deps.nodes.filter(_.typ == "stage").map(_.value)
    st1
  }

  def eval(manifest: Manifest): EvaluatedManifest = {
    val st = stageExpansion(evalLoop(evalManifest(emptyState, manifest)))
    EvaluatedManifest(st.resources, st.deps)
  }
}
