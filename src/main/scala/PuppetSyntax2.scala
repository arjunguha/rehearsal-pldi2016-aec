package rehearsal

object PuppetSyntax2 {

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

  sealed trait Resource
  case class ResourceDecl(typ: String, resources: Seq[(Expr, Seq[Attribute])]) extends Resource
  case class ResourceRef(typ: String, title: Expr, attrs: Seq[Attribute]) extends Resource

  sealed trait Case
  case class CaseDefault(m: Manifest) extends Case
  case class CaseExpr(e: Expr, m: Manifest) extends Case

  sealed trait Manifest
  case object Empty extends Manifest
  case class Block(m1: Manifest, m2: Manifest) extends Manifest
  case class EdgeList(resources: Seq[Resource]) extends Manifest
  case class Define(name: String, params: Seq[Argument], body: Manifest) extends Manifest
  case class Class(name: String, params: Seq[Argument], inherits: Option[String], body: Manifest) extends Manifest
  case class ESet(varName: String, e: Expr) extends Manifest
  case class MCase(e: Expr, cases: Seq[Case]) extends Manifest
  case class ITE(pred: Expr, m1: Manifest, m2: Manifest) extends Manifest
  case class Include(e: Expr) extends Manifest
  case class Require(e: Expr) extends Manifest
  case class MApp(name: String, args: Seq[Expr]) extends Manifest

   // Manifests must not appear in Expr, either directly or indirectly
  sealed trait Expr
  case object Undef extends Expr
  case class Str(s: String) extends Expr
  case class Num(n: Int) extends Expr
  case class Var(name: String) extends Expr
  case class Bool(b: Boolean) extends Expr
  case class Not(e: Expr) extends Expr
  case class And(e1: Expr, e2: Expr) extends Expr
  case class Or(e1: Expr, e2: Expr) extends Expr
  case class Eq(e1: Expr, e2: Expr) extends Expr
  case class Match(e1: Expr, e2: Expr) extends Expr
  case class In(e1: Expr, e2: Expr) extends Expr
  case class Array(es: Seq[Expr]) extends Expr
  case class App(name: String, args: Seq[Expr]) extends Expr
  case class Regex(regex: String) extends Expr
  case class Cond(test: Expr, truePart: Expr, falsePart: Expr) extends Expr
  case class EResourceRef(typ: String, title: Expr) extends Expr

}
