package rehearsal

object PuppetSyntax {

  import scala.util.parsing.input.Positional
  import scalax.collection.Graph
  import scalax.collection.GraphEdge.DiEdge
  import Implicits._

  // Documentation states that include can accept:
  //   * a single class name (apache) or a single class reference (Class['apache'])
  //   * a comma separated list of class names or class references
  //   * an array of class names or class references
  //  Examples:
  //  include base::linux
  //  include Class['base::linux'] # including a class reference
  //  include base::linux, apache # including a list
  //  $my_classes = ['base::linux', 'apache']
  //  include $my_classes # including an array
  //
  //  NOTE: The parser tests only include the first of these three
  //
  // The main difference between include and require is that require
  // causes the surrounding container to have a dependency on that class.
  // That is, all of the resources in the class are guaranteed to
  // have been applied before the surrounding structure is instantiated
  // Another difference is that requiring the same class twice is actually
  // a runtime error.


  case class Attribute(name: Expr, value: Expr)
  case class Argument(id: String, default: Option[Expr]) //ignoring types for now

  sealed trait Resource extends Positional
  case class ResourceDecl(typ: String, resources: Seq[(Expr, Seq[Attribute])]) extends Resource
  case class ResourceRef(typ: String, title: Expr, attrs: Seq[Attribute]) extends Resource

  sealed trait Case extends Positional
  case class CaseDefault(m: Manifest) extends Case
  case class CaseExpr(e: Expr, m: Manifest) extends Case

  sealed trait Manifest extends Positional {
   def eval(): EvaluatedManifest = PuppetEval.eval(this)
  }

  case object MEmpty extends Manifest
  case class MSeq(m1: Manifest, m2: Manifest) extends Manifest
  case class MResources(resources: Seq[Resource]) extends Manifest
  case class MDefine(name: String, params: Seq[Argument], body: Manifest) extends Manifest
  case class MClass(name: String, params: Seq[Argument], inherits: Option[String], body: Manifest) extends Manifest
  case class MSet(varName: String, e: Expr) extends Manifest
  case class MCase(e: Expr, cases: Seq[Case]) extends Manifest
  case class MIte(pred: Expr, m1: Manifest, m2: Manifest) extends Manifest
  case class MInclude(es: List[Expr]) extends Manifest
  case class MRequire(e: Expr) extends Manifest
  case class MApp(name: String, args: Seq[Expr]) extends Manifest

   // Manifests must not appear in Expr, either directly or indirectly
  sealed trait Expr extends Positional
  case object EUndef extends Expr
  case class EStr(s: String) extends Expr
  case class ENum(n: Int) extends Expr
  case class EVar(name: String) extends Expr
  case class EBool(b: Boolean) extends Expr
  case class ENot(e: Expr) extends Expr
  case class EAnd(e1: Expr, e2: Expr) extends Expr
  case class EOr(e1: Expr, e2: Expr) extends Expr
  case class EEq(e1: Expr, e2: Expr) extends Expr
  case class ELT(n1: Expr, n2: Expr) extends Expr
  case class EMatch(e1: Expr, e2: Expr) extends Expr
  case class EIn(e1: Expr, e2: Expr) extends Expr
  case class EArray(es: Seq[Expr]) extends Expr
  case class EApp(name: String, args: Seq[Expr]) extends Expr
  case class ERegex(regex: String) extends Expr
  case class ECond(test: Expr, truePart: Expr, falsePart: Expr) extends Expr
  case class EResourceRef(typ: String, title: Expr) extends Expr

  // Our representation of fully evaluataed manifests, where nodes are primitive resources.
  case class EvaluatedManifest(ress: Map[Node, ResourceVal], deps: Graph[Node, DiEdge]) {
    def resourceGraph(): ResourceGraph = ResourceGraph(ress.mapValues(x => ResourceSemantics.compile(x)), deps)

  }

  case class ResourceVal(typ: String, title: String, attrs: Map[String, Expr]) {
    val node = Node(typ, title)
  }

  case class Node(typ: String, title: String) {
    lazy val isPrimitiveType = PuppetEval.primTypes.contains(typ)
  }

  case class ResourceGraph(ress: Map[Node, ResourceModel.Res], deps: Graph[Node, DiEdge]) {

    def fsGraph(): FileScriptGraph = FSGraph(ress.mapValues(_.compile()), deps)


  }

  // A potential issue with graphs of FS programs is that several resources may compile to the same FS expression.
  // Slicing makes this problem more likely. To avoid this problem, we keep a map from unique keys to expressions
  // and build a graph of the keys. The actual values of the keys don't matter, so long as they're unique.
  // PuppetSyntax.Node is unique for every resource, so we use that when we load a Puppet file. For testing,
  // the keys can be anything.
  case class FSGraph[K](exprs: Map[K, FSSyntax.Expr], deps: Graph[K, DiEdge]) {

    lazy val size: Int = {
      deps.nodes.map(n => exprs(n).size).reduce(_ + _) + deps.edges.size
    }

    /** Returns an FS program that represents the action of a <b>deterministic</b> graph.
      *
      * @return an FS program
      */
    def expr(): FSSyntax.Expr = {
      FSSyntax.Block(deps.topologicalSort().map(k => exprs(k)): _*)
    }

    /** Checks if two <b>deterministic</b> FS graphs are equivalent.
      *
      * @param other the other FS graph
      * @return [None] if they are equivalent and [Some cex] if they are not and [cex] witnesses the difference
      */
    def notEquiv(other: FSGraph[K]): Option[FSEvaluator.State] = {
      SymbolicEvaluator.exprEquals(this.expr(), other.expr())
    }

  }

  type FileScriptGraph = FSGraph[Node]


}
