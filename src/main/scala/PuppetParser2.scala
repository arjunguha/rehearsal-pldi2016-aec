package rehearsal

import scala.util.parsing.combinator._
import PuppetSyntax2._
import Implicits._

class PuppetParser2 extends RegexParsers with PackratParsers {

  type P[T] = PackratParser[T]

  override protected val whiteSpace = """(\s|#.*|(/\*((\*[^/])|[^*])*\*/))+""".r

  // TODO(arjun): escape sequences? interpolation?
  lazy val stringVal: P[String] =
    "\"" ~> "[^\"]*".r <~ "\"" |
    "'" ~> "[^']*".r <~ "'"
  lazy val word: P[String] = "(::)?[a-zA-Z]([a-zA-Z_]*(::)?[a-zA-Z]+)*".r ^^ {case x => x}
  lazy val id: P[String] = "" ~> "[a-z_][a-zA-Z0-9_]*".r
  lazy val attributeName: P[String] = "" ~> "[a-z]+".r
  lazy val dataType: P[String] = "" ~> "[A-Z][a-zA-Z]+".r
  lazy val varName: P[String] =  "$" ~> "[a-z_(::)][a-zA-Z0-9_(::)]*[a-zA-Z0-9_]+|[a-z_(::)]".r

  lazy val className: P[Expr] = expr | word ^^ (Str(_))

  //Manifest
  lazy val manifest: P[Manifest] = positioned {
    varName ~ "=" ~ expr ^^
      { case x ~ _ ~ e => ESet(x, e) } |
    "define" ~ word ~ params ~ body ^^
      { case _ ~ x ~ xs ~ m => Define(x, xs, m) } |
    "class" ~ word ~ params ~ body ^^
      { case _ ~ x ~ xs ~ m => Class(x, xs, None, m) } |
    "class" ~ word ~ params ~ "inherits" ~ word ~ body ^^
      { case _ ~ x ~ xs ~ _ ~ y ~ m => Class(x, xs, Some(y), m) } |
    "case" ~ expr ~ "{" ~ cases ~ "}" ^^
      { case _ ~ e ~ _ ~ lst ~ _ => MCase(e, lst) } |
    "include" ~ repsep(className, ",") ^^
      { case _ ~ xs => Include(xs) } |
    "require" ~ className ^^
      { case _ ~ x => Require(x) } |
    "if" ~ expr ~ body ~ elses ^^
      { case _ ~ e ~ m1 ~ m2 => ITE(e, m1, m2) } |
    rep1sep(resource, "->") ^^
      { case lst => EdgeList(lst) } |
    word ~ "(" ~ repsep(expr, ",") ~ ")" ^^
      { case f ~ _ ~ xs ~ _  => MApp(f, xs) }
    }

  lazy val elses: P[Manifest] = positioned {
    "else" ~ body ^^
      { case _ ~ m => m } |
    "elsif" ~ parenExpr ~ body ~ elses ^^
      { case _ ~ e ~ m1 ~ m2 => ITE(e, m1, m2) } |
    success(()) ^^
      { case () => Empty }
    }

  lazy val body: P[Manifest] = "{" ~> prog <~ "}"

  lazy val prog: P[Manifest] = rep(manifest) ^^ { case exprs => blockExprs(exprs) }

  def blockExprs(exprs: Seq[Manifest]): Manifest = {
    exprs.foldRight[Manifest](Empty) { case (m1, m2) => Block(m1, m2) }
  }

  lazy val cases: P[Seq[Case]] =
    "default" ~ ":" ~ body ^^ { case _ ~ _ ~ m => Seq(CaseDefault(m)) } |
    expr ~ ":" ~ body ~ cases ^^ { case e ~ _ ~ m ~ rest => CaseExpr(e, m) +: rest } |
    success(()) ^^ { case _ => Seq[Case]() }

  lazy val parameter: P[Argument] = opt(dataType) ~ varName ~ opt("=" ~> expr) ^^ {
    case typ ~ id ~ Some(default) => Argument(id, Some(default))
    case typ ~ id ~ None => Argument(id, None)
  }

  lazy val params: P[Seq[Argument]] =
    ("(" ~> repsep(parameter, ",") <~ opt(",")) <~ ")" |
    success(()) ^^ { case _ => Seq[Argument]() }

  lazy val edges: P[Seq[Resource]] =
    resource ~ "->" ~ edges ^^
      { case x ~ _ ~ xs => x +: xs } |
    resource ^^
      { case x => Seq(x) }

  lazy val resource: P[Resource] =
    word ~ "{" ~ rep1sep(resourcePair, ";") ~ opt(";") ~ "}" ^^
      { case typ ~ _ ~ lst ~ _ ~ _ => ResourceDecl(typ, lst) } |
    word ~ "[" ~ expr ~ "]" ~ "{" ~ attributes ~ "}" ^^
      { case typ ~ _ ~ title ~ _ ~ _ ~ attrs ~ _ => ResourceRef(typ, title, attrs) } |
    word ~ "[" ~ expr ~ "]" ^^
      { case typ ~ _ ~ title ~ _ => ResourceRef(typ, title, Seq()) }

  lazy val resourcePair: P[(Expr, Seq[Attribute])] = (expr <~ ":") ~ attributes ^^ {
    case id ~ attr => (id, attr)
  }

  //Attribute
  lazy val attrId: P[Str] = id ^^ { case s => Str(s) }
  lazy val attribute: P[Attribute] =
    (attrId | vari) ~ ("=>" ~> (expr | attrId)) ^^ { case name ~ value => Attribute(name, value) }

  lazy val attributes: P[Seq[Attribute]] = repsep(attribute, ",") <~ opt(",")

  lazy val vari: P[Expr] = varName ^^ (Var(_))

  //
  // Expressions. Use "expr" to parse an expression. Do not use any of the other
  // parsers (e.g., atom, bop, etc.) outside this block.
  //

  lazy val parenExpr: P[Expr] = "(" ~ expr ~ ")" ^^ { case _ ~ e ~ _ => e }

  lazy val atom: P[Expr] = positioned {
    "undef" ^^ { _ => Undef } |
    "true" ^^ { _ => Bool(true) } |
    "false" ^^ { _ => Bool(false) } |
    vari |
    stringVal ^^ { x => Str(x) } |
    """\d+""".r ^^
      { n => Num(n.toInt) } |
    "[" ~ repsep(expr, ",") ~ opt(",") ~ "]" ^^ { case _ ~ es ~ _ ~ _ => Array(es) } |
    word ~ "(" ~ repsep(expr, ",") ~ ")" ^^ { case f ~ _ ~ xs ~ _  => App(f, xs) } |
    ("/" ~> "[^/]*".r <~ "/") ^^ { case expr => Regex(expr) } |
    word ~ "[" ~ expr ~ "]" ^^
      { case typ ~ _ ~ title ~ _ => EResourceRef(typ, title) } |
    parenExpr
  }

  lazy val not: P[Expr] = positioned {
    "!" ~> not ^^ { Not(_) } |
    atom
  }

  lazy val and: P[Expr] = positioned {
    not ~ "and" ~ and ^^ { case lhs ~ _ ~ rhs => And(lhs, rhs) } |
    not
  }

  lazy val or: P[Expr] = positioned {
    and ~ "or" ~ or ^^ { case lhs ~ _ ~ rhs => Or(lhs, rhs) } |
    and
  }

  lazy val bop: P[Expr] = positioned {
    or ~ "==" ~ bop ^^ { case lhs ~ _ ~ rhs => Eq(lhs, rhs) } |
    or ~ "!=" ~ bop ^^ { case lhs ~ _ ~ rhs => Not(Eq(lhs, rhs)) } |
    or ~ "<" ~ bop ^^ { case lhs ~ _ ~ rhs => LT(lhs, rhs) } |
    or ~ ">" ~ bop ^^ { case lhs ~ _ ~ rhs => LT(rhs, lhs) } |
    or ~ "<=" ~ bop ^^ { case lhs ~ _ ~ rhs => Or(LT(lhs, rhs), Eq(lhs, rhs)) } |
    or ~ ">=" ~ bop ^^ { case lhs ~ _ ~ rhs => Or(LT(rhs, lhs), Eq(lhs, rhs)) } |
    or ~ "=~" ~ bop ^^ { case lhs ~ _ ~ rhs => Match(lhs, rhs) } |
    or ~ "!~" ~ bop ^^ { case lhs ~ _ ~ rhs => Not(Match(lhs, rhs)) } |
    or ~ "in" ~ bop ^^ { case lhs ~ _ ~ rhs => In(lhs, rhs) } |
    or
  }



  lazy val cond: P[Expr] = positioned {
    bop ~ "?" ~ bop ~ ":" ~ cond ^^
      { case e1 ~ _ ~ e2 ~ _ ~ e3 => Cond(e1, e2, e3) } |
    "if" ~ bop ~ "{" ~ expr ~ "}" ~ "else" ~ "{" ~ expr ~ "}" ^^
      { case _ ~ e1 ~ _ ~ e2 ~ _ ~ _ ~ _ ~ e3 ~ _ => Cond(e1, e2, e3) } |
    bop
  }


  lazy val expr: P[Expr] = cond

}

object PuppetParser2 {
  private val parser = new PuppetParser2()
  import parser._

  def parse(str: String): Manifest = parseAll(prog, str) match {
    case Success(r, _) => r
    case m => throw new ParseError(s"$m")
  }

  def parseFile(filename: String): Manifest = {
    import java.nio.file._
    parse(new String(Files.readAllBytes(Paths.get(filename))))
  }


}
