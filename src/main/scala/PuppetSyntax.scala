package rehearsal

object Syntax {

  case class Attribute(name: Expr, value: Expr)
  case class Argument(id: String, default: Option[Expr]) //ignoring types for now

  sealed trait Manifest
  case object Empty extends Manifest
  case class Block(m1: Manifest, m2: Manifest) extends Manifest
  case class Resource(title: Expr, typ: String, attrs: Seq[Attribute]) extends Manifest
  case class Edge(m1: Manifest, m2: Manifest) extends Manifest
  case class Define(name: String, params: Seq[Argument], body: Manifest) extends Manifest
  case class Class(name: String, params: Seq[Argument], inherits: Option[String], body: Manifest) extends Manifest
  case class Let(varName: String, e: Expr, body: Manifest) extends Manifest
  case class MCase(e: Expr, cases: Seq[Case]) extends Manifest
  case class E(e: Expr) extends Manifest

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
  case class Include(e: Expr) extends Manifest
  
  // The main difference between include and require is that require
  // causes the surrounding container to have a dependency on that class.
  // That is, all of the resources in the class are guaranteed to
  // have been applied before the surrounding structure is instantiated
  // Another difference is that requiring the same class twice is actually
  // a runtime error.
  case class Require(e: Expr) extends Manifest


  sealed trait Expr
  case class Str(s: String) extends Expr
  case class Res(typ: String, e: Expr, attrs: Seq[Attribute]) extends Expr
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
  case class ITE(pred: Expr, m1: Manifest, m2: Manifest) extends Expr

  // From the Language: Data Types: Regular Expressions
  // https://docs.puppetlabs.com/puppet/latest/reference/lang_data_regexp.html
  // A regular expression can have these options sprinkled through out. In
  // practice it seems that these are placed at the beginning of the expression
  // For example: /(?{enabled-options}-{disabled-options}:regex)/ 
  // TODO(jcollard): This will not cut it for arbitrary puppet regexps because
  // it is only picking up the initial options.
  case class RegExp(options: Seq[RegExpOption], regexp: String) extends Expr

  sealed trait RegExpOption
  // Ignores case in the regexp 'i'
  case object IgnoreCase extends RegExpOption
  // Matches newlines on the regular expression '.'
  case object MatchNewLine extends RegExpOption
  // Ignores white spaces and comments in the regular expression 'x'
  case object IgnoreWhiteSpace extends RegExpOption

  sealed trait Case
  case class CaseDefault(m: Manifest) extends Case
  case class CaseExpr(e: Expr, m: Manifest) extends Case
}
