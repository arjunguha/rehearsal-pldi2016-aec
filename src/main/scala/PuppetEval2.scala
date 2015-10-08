package rehearsal

object PuppetEval2 {

  import PuppetSyntax2._
  import scalax.collection.Graph
  import scalax.collection.Graph._
  import scalax.collection.GraphPredef._
  import scalax.collection.GraphEdge._
  import scalax.collection.edge.Implicits._

  val primTypes =  Set("file", "File", "package", "Package", "user", "User",
    "group", "Group", "service", "Service", "ssh_authorized_key",
    "Ssh_authorized_key")


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
        val nodes = vals.map(_.node)
        val redefinedResources = st.resources.keySet.intersect(nodes.toSet)
        if (redefinedResources.isEmpty == false) {
          throw EvalError(s"${redefinedResources.head} is already defined")
        }
        else {
          val newResources = vals.map(r => r.node -> r).toMap
          (st.copy(resources = st.resources ++ newResources), nodes.toList)
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
    case v => throw EvalError(s"predicate evaluated to $v")
  }

  def evalExpr(env: Env, expr: Expr): Expr = expr match {
    case Undef => Undef
    case Num(n) => Num(n)
    case Str(str) => Str(str)
    case Bool(b) => Bool(b)
    case EResourceRef(typ, title) => EResourceRef(typ, evalExpr(env, title))
    case Eq(e1, e2) => Bool(evalExpr(env, e1) == evalExpr(env, e2))
    case Not(e) => Bool(!evalBool(env, e))
    case Var(x) => env.get(x) match {
      case Some(v) => v
      case None => throw EvalError(s"variable $x is undefined")
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

def evalLoop(st: State, manifest: Manifest) = {
  val st1 = evalManifest(st, manifest)
  st1.deps.nodes.find(node => node.typ == "class") match {
    case None => st1
    case Some(node) => {
      node.value match {
        case Node(_, name) => {
          throw EvalError(s"need to expand class $name")
        }
      }
    }
  }
}

  def eval(manifest: Manifest): (Map[Node, ResourceVal], Graph[Node, DiEdge]) = {
    val st = evalLoop(State(Map(), Graph.empty, Map(), Map(), Map()),
                          manifest)
    (st.resources, st.deps)
  }

}