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

  val primTypes =  Set("file", "File", "package", "Package", "user", "User",
    "group", "Group", "service", "Service", "ssh_authorized_key",
    "Ssh_authorized_key", "augeas", "Augeas")


  case class ResourceVal(typ: String, title: String, attrs: Map[String, Expr]) {

    val node = Node(typ, title)
  }

  type Env = Map[String, Expr]

  case class Node(typ: String, title: String)

  case class State(resources: Map[Node, ResourceVal],
                   deps: Graph[Node, DiEdge],
                   env: Env,
                   definedTypes: Map[String, Manifest],
                   classes: Map[String, Manifest])



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

  // Produces a new state and a list of resource titles
  // TODO(arjun): Handle "require" and "before" dependencies.
  def evalResource(st: State, resource: Resource): (State, List[Node]) = {
    resource match {
      case ResourceRef(typ, titleExpr, Seq()) => {
        val node = Node(typ, evalTitle(st.env, titleExpr))
        (st.copy(deps = st.deps + node), List(node))
      }
      case ResourceDecl(typ, lst) => {
        val vals = lst.map { case (titleExpr, attrs) =>
          ResourceVal(typ, evalTitle(st.env, titleExpr),
                      evalAttrs(st.env, attrs))
        }
        val newNodes: Set[Node] = vals.map(_.node).toSet
        //println(s"Creating nodes $nodes")
        val redefinedResources = st.resources.keySet.intersect(newNodes)
        if (redefinedResources.isEmpty == false) {
          throw EvalError(s"${redefinedResources.head} is already defined")
        }
        else {
          val newResources = vals.map(r => r.node -> r).toMap
          (st.copy(resources = st.resources ++ newResources,
                   deps = st.deps ++ Graph.from(newNodes, edges = Set())),
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
        st.copy(definedTypes = st.definedTypes + (f -> manifest))
      }
    }
    case Class(f, args, _, m) => {
      if (st.classes.contains(f)) {
        throw EvalError(s"$f is already defined as a class")
      }
      else {
        st.copy(classes = st.classes + (f -> manifest))
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
    case MCase(e, cases) => {
      val v = evalExpr(st.env, e)
      cases.find(c => matchCase(st.env, v, c)) match {
        case None => st
        case Some(CaseDefault(m)) => evalManifest(st, m)
        case Some(CaseExpr(_, m)) => evalManifest(st, m)
      }
    }

    case _ => throw NotImplemented(manifest.toString)
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
    case EResourceRef(typ, title) => EResourceRef(typ, evalExpr(env, title))
    case Eq(e1, e2) => Bool(evalExpr(env, e1) == evalExpr(env, e2))
    case Not(e) => Bool(!evalBool(env, e))
    case Var(x) => env.get(x) match {
      case Some(v) => v
      case None => Undef
    }
    case Array(es) => Array(es.map(e => evalExpr(env, e)))
    case App("template", Seq(e)) => evalExpr(env, e) match {
      // TODO(arjun): This is bogus. It is supposed to use filename as a
      // template string. The file contents have patterns that refer to variables
      // in the environment.
      case Str(filename) => Str(filename)
      case _ => throw EvalError("template function expects a string argument")
    }
    case Cond(e1, e2, e3) => evalBool(env, e1) match {
      case true => evalExpr(env, e2)
      case false => evalExpr(env, e3)
    }
    case _ => throw NotImplemented(expr.toString)
  }

//   case class Set(varName: String, e: Expr) extends Manifest
//   case class MCase(e: Expr, cases: Seq[Case]) extends Manifest
//   case class ITE(pred: Expr, m1: Manifest, m2: Manifest) extends Manifest
//   case class Include(e: Expr) extends Manifest
//   case class Require(e: Expr) extends Manifest
//   case class MApp(name: String, args: Seq[Expr]) extends Manifest

// }

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
    st.classes.get(title) match {
      case Some(Class(_, _, _, m)) => {
        val st1 = evalManifest(st.copy(deps = Graph.empty), m)
        val classNode = st.deps.get(Node("class", title))
        st1.copy(deps = splice(st.deps, st.deps.get(Node("class", title)), st1.deps))
      }
      case None => throw EvalError(s"class not found: $title ${st.classes.keys}")
      case _ => throw new Exception("expected class")
    }
  }

  def instantiateType(st: State, node: Node): State = {
    val Define(_, formals, m) = st.definedTypes(node.typ)
    val ResourceVal(_, _, actuals) = st.resources(node)
    val expected = formals.map(x => x.id -> x.default).toMap
    val unexpected = actuals.keySet -- expected.keySet
    if (unexpected.isEmpty == false) {
      throw EvalError(s"unexpected arguments: ${unexpected}")
    }
    val titlePair = ("title" -> Str(node.title))
    val evaluated = expected.map {
      case (x, None) => actuals.get(x) match {
        case Some(v) => (x, v)
        case None => throw EvalError(s"expected argument $x")
      }
      case (x, Some(default)) => actuals.get(x) match {
        case Some(v) => (x, v)
        case None => (x, evalExpr(st.env + titlePair, default))
      }
    }
    val st1 = evalManifest(st.copy(deps = Graph.empty,
                                   env = evaluated.toMap + titlePair),
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
    classes = Map())

  def eval(manifest: Manifest): (Map[Node, ResourceVal], Graph[Node, DiEdge]) = {
    val st = evalLoop(evalManifest(emptyState, manifest))
    (st.resources, st.deps)
  }

}
