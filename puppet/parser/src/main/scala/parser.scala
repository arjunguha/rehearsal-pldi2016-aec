package puppet.parser

import puppet._
import puppet.syntax._
import scala.util.parsing.combinator._
import scala.util.parsing.combinator.syntactical._
import scala.util.parsing.combinator.lexical._
import scala.util.parsing.combinator.token._
import scala.util.parsing.input.CharArrayReader.EofCh
import scala.util.parsing.input.Reader
import scala.util.parsing.input.Position
import collection.mutable.HashSet

private trait PuppetTokens extends StdTokens {

  case class PuppetBool (chars: String) extends Token {
    override def toString = s"'${chars}'"
  }

  case class PuppetName (chars: String) extends Token {
    override def toString = s"PuppetName: $chars"
  }

  case class PuppetClassRef (chars: String) extends Token {
    override def toString = s"PuppetClassRef: $chars"
  }

  case class PuppetRegex (chars: String) extends Token {
    override def toString = s"PuppetRegex: $chars"
  }

  case class PuppetVariable (chars: String) extends Token {
    override def toString = s"PuppetVariable: $chars"
  }

  case class PuppetInterpolation (parts: List[String]) extends Token {
    override def toString = s"PuppetInterpolation: $chars"
    override def chars = "\"%s\"".format(parts mkString "")
  }
}

private trait PuppetLexical extends Scanners with PuppetTokens {
  def tokenize(s: String): Reader[Token]
}

private class ProgramLexer extends StdLexical
                           with RegexParsers
                           with PuppetLexical {
  override type Elem = Char

  def tokenize(s: String): Reader[Token] = new Scanner(s)

  override val delimiters =
    HashSet("<-", "->", "<~", "~>",
           "(", ")", "{", "}", "[", "]",
           ",", ";", ":", ".",
           "@@", "@", "<|", "|>", "<<|", "|>>",
           "=>", "==", "!=", "=", "+=", "+>", "!", "=~", "!~", "?",
           "+", "-", "/", "*", "%", "<<", ">>", ">", "<", ">=", "<=")

  override val reserved =
    HashSet("and" , "case" , "class" , "default" ,
            "define" , "else" , "elsif" , "if" , "in" , "import" , "inherits" ,
            "node" , "or" , "undef" , "unless")

  var ctx : Token = EOF

  /* Regex can only appear after these keywords in grammar, otherwise
   * regex containing symbols '/.../' are treated as mathematical divide
   */
  val regexCtx = List(Keyword("node"), Keyword("{"), Keyword("}"),
                      Keyword("=~"), Keyword("!~"), Keyword(","))

  private def matchCtx(ctx: Token, tests: List[Token]): Boolean =
    tests.exists(_ == ctx)

  override def token(): Parser[Token] = (
      NAMETOK ^^ (processName (_))
    | CLASSREF ^^ (PuppetClassRef (_))
      // Regex can only appear in certain contexts
    | '/' ~ regexTok(ctx) ~ '/' ^^ { case '/' ~ reg ~ '/' => PuppetRegex ("/%s/".format (reg)) }
    | '$' ~> VARIABLETOK ^^ (PuppetVariable(_))
    | '\'' ~> stringLit ('\'') <~ '\'' ^^ { str => StringLit("\'" + str + "\'") }
    | '\"' ~> interpolation <~ '\"' ^^ { parts => PuppetInterpolation(parts) }
    | '\"' ~> stringLit ('\"') <~ '\"' ^^ { str => StringLit("\"" + str + "\"") }
    | '\'' ~> failure("unclosed string literal")
    | '\"' ~> failure("unclosed string literal")
    | delim
    | failure("illegal character")) map {res => ctx = res; res}

  private def interpolation: Parser[List[String]] =
    (partInterpolation).+ ~ postInterpolation ^^ {
      case pl ~ postInterp => {
        val pinterp = (("\"" + pl.head._1), pl.head._2) :: pl.tail
        ((postInterp + "\"") :: (pinterp.foldLeft(List[String]()) ({ case(acc, elem) => elem._2 :: (elem._1) :: acc}))).reverse
      }
    }

  private def partInterpolation: Parser[(String, String)] = (
    preInterpolationBraces ~ inInterpolation ^^ { case str ~ e => (str, "${" + e + "}") }
  | preInterpolationNoBraces ~ VARIABLETOK ^^ { case str ~ v => (str, "${" + v + "}") } // equivalent
  )

  private def preInterpolationBraces: Parser[String] = (
    rep(chrExcept('\\', '\"', '$')) ~ escapeSeq ~ preInterpolationBraces ^^ { case chars ~ es ~ interpstr => (chars mkString "") + es + interpstr }
  | rep(chrExcept('\"', '$', EofCh)) <~ '$' <~ '{' ^^ (_ mkString "")
  )

  private def preInterpolationNoBraces: Parser[String] = (
    rep (chrExcept ('\\', '\"', '$')) ~ escapeSeq ~ preInterpolationNoBraces ^^ { case chars ~ es ~ interpstr => (chars mkString "") + es + interpstr }
  | rep (chrExcept ('\"', '$', EofCh)) <~ '$' ^^ (_ mkString "")
  )

  private def inInterpolation: Parser[String] =
    rep(chrExcept('}', EofCh)) <~ '}' ^^ (_ mkString "")

  private def postInterpolation: Parser[String] = stringLit('\"')

  protected def stringLit(quote_char: Char): Parser[String] = (
    rep (chrExcept ('\\', quote_char))  ~ escapeSeq ~ stringLit (quote_char) ^^ { case chars ~ es ~ strlit => (chars mkString "") + es + strlit }
  | rep (chrExcept (quote_char, EofCh)) ^^ (_ mkString "")
  )

  private def escapeSeq: Parser[String] = '\\' ~ chrExcept (EofCh) ^^ { case '\\' ~ ch => "\\" + ch }

  private def regexTok (ctx: Token): Parser[String] =
    if (matchCtx(ctx, regexCtx))
      (
        rep(chrExcept('\\', '/', EofCh, '\n')) ~ '\\' ~ '/' ~ regexTok(ctx) ^^ { case chars ~ '\\' ~ '/' ~ reg => (chars mkString "") + "\\/" + reg }
      | rep(chrExcept('\\', '/', EofCh, '\n')) ~ '\\' ~ regexTok(ctx) ^^ { case chars ~ '\\' ~ reg => (chars mkString "") + "\\" + reg }
      | rep(chrExcept('\\', '/', EofCh, '\n')) ^^ (_ mkString "")
      )
   else failure("context not matching")

  private def processName (name: String) =
    if (reserved contains name) Keyword (name)
    else if ("true" == name || "false" == name) PuppetBool (name)
    else PuppetName (name)

  override def whitespace: Parser[Any] = rep[Any](
    whitespaceChar
  | '/' ~ '*' ~ comment
  | '#' ~ rep ( chrExcept (EofCh, '\n'))
  | '/' ~ '*' ~ failure ("unclosed comment")
  )

  override def comment: Parser[Any] = (
      rep(chrExcept(EofCh, '*')) ~ '*' ~ '/' ^^ { _ => ' ' }
    | rep(chrExcept(EofCh, '*')) ~ '*' ~ comment ^^ { _ => ' ' }
  )

  protected def BOOLEAN: Parser[String] = ("true" | "false")

  protected def NAMETOK: Parser[String] = ("""((::)?[a-z0-9][-\w]*)(::[a-z0-9][-\w]*)*""".r
                           ||| NUMBER)

  protected def NUMBER:Parser[String] = """\b(?:0[xX][0-9A-Fa-f]+|0?\d+(?:\.\d+)?(?:[eE]-?\d+)?)\b""".r

  protected def CLASSREF: Parser[String] = """((::){0,1}[A-Z][-\w]*)+""".r

  protected def VARIABLETOK: Parser[String] = (
    """(?:::)?(?:[-\w]+::)*[-\w]+""".r // VAR_WITH_DASH
  | """(::)?(\w+::)*\w+""".r           // Simple VAR
  )
}



/* When interpolating the following rules are observed by original puppet parser
 *
 * - Variables can occur with and without '$' prefix when interpolating
 *
 * - A complex expression can occur inside interpolation
 *
 * - The first and *ONLY* first token inside interpolation is parsed as a
 *   variable, irrespective of whether its a boolean, a reserved keyword or
 *   a number
 *   The only exception to this rule is quoted string.
 * - If parsing it as variable fails then a syntax error is raised
 *
 *  Ex: $y = 1
 *      notice("${y + '1'}") gives '2', y is interpolated as variable
 *      notice("${'1' + y}") gives error, as y is not interpolated as a variable
 *
 *  Ex: $x = 1
 *      $y = 2
 *      notice("${ x + y }")
 *  The above code fragment raises an error that y is not a number, becuase 'x'
 *  is parsed as a variable while y is not
 *
 *  Ex: notice("${1.2 + 3}") raises error as 1.2 cannot be parsed as a variable
 *
 *  Ex: $one = "particular"
 *      $another = "particular"
 *      notice("${one == another}") gives 'false' because while 'one' is
 *      interpolated as a variable, 'another' is not.
 *      notice("${one == 'particular'}") gives 'true'
 */
 // Currently only lexing on the first token
private class VariableLexer extends ProgramLexer {
  override def token: Parser[Token] = (VARIABLETOK | '$'~>VARIABLETOK) ^^ (PuppetVariable(_))
}


/*
private class InterpolateLexer extends PuppetLexical {

  override def token: Parser[Token] = failure("token method not valid")
  override def whitespace = failure("whitespace not valid")

  class InterpolateScanner(in: List[(Token, Position)])
                          (implicit val lastpos: Position) extends Reader[Token] {
    override def first = in.head._1
    override def rest = if(atEnd) this else (new InterpolateScanner(in.tail))
    override def pos = if(atEnd) lastpos else in.head._2
    override def atEnd = in.isEmpty
    // override def source = throw new Exception("I thought source method is not required")
    // override def offset = throw new Exception("I thought offset method is not required")
  }

  // expected to be a small string, we can tokenize before hand
  override def tokenize(s: String): Reader[Token] = {
    // val varlexer = new VariableLexer
    val proglexer = new ProgramLexer

    var progscanner = proglexer.tokenize(s)
    // val varscanner = varlexer.tokenize(s)
    var toklist: List[(Token, Position)] = List() // List((varscanner.first.asInstanceOf[this.Token], varscanner.pos))
    // val rest = varscanner.rest
    //val restOfInput = rest.source.subSequence(rest.offset, s.length).toString
    //println ("Rest: " + restOfInput)
    // var progscanner = proglexer.tokenize(" " + restOfInput)
    while (!progscanner.atEnd) {
      toklist = (progscanner.first.asInstanceOf[Token], progscanner.pos) :: toklist
      progscanner = progscanner.rest
    }

    toklist.reverse.foreach(println(_))
    val lastpos = toklist.head._2

    println("IsKeyword: " + toklist(0)._1.isInstanceOf[Keyword])
    println("Length of keyword: " + toklist(0)._1.chars.length)
    println("Keyword chars: " + toklist(0)._1.chars)
    println("Keyword tostr: " + toklist(0)._1.toString)

    new InterpolateScanner(toklist.reverse)(lastpos)
  }
}
*/

private class PuppetParser(lexer: PuppetLexical) extends StdTokenParsers with PackratParsers {

  type Tokens = PuppetTokens
  override val lexical = lexer

  type P[+T] = PackratParser[T]

  lazy val topLevel: P[TopLevelConstruct] =
    (stmt | definition | hostclass | nodedef)

  lazy val program: P[TopLevel] = topLevel.* ^^ (TopLevel(_))

  lazy val stmts_and_decls: P[BlockStmtDecls] = (stmt | decl).* ^^ (BlockStmtDecls (_))

  lazy val decl: P[ClassBody] = definition | hostclass

  lazy val stmt: P[Statement] = (
    (resource ||| resource_defaults ||| relationship ||| resourceoverride ) |
    virtualresource |
    collection | assignment | case_stmt | ifstmt | unless_stmt |
    import_stmt | fstmt | append
  )

  lazy val relationship: P[RelationExpr] =
    relationship_side ~ (("<-" | "->" | "<~" | "~>") ~ relationship_side).+ ^^ {
      case rs ~ rss => (rss.foldLeft (rs) {
          case (x, "<-" ~ y) => RelationExpr (x, y, LeftSimpleDep)
          case (x, "->" ~ y) => RelationExpr (x, y, RightSimpleDep)
          case (x, "<~" ~ y) => RelationExpr (x, y, LeftSubscribeDep)
          case (x, "~>" ~ y) => RelationExpr (x, y, RightSubscribeDep)
        }).asInstanceOf [RelationExpr]
      }

  lazy val relationship_side: P[RelationExprOperand] = (
    resource ||| resourceref ||| collection ||| variable ||| selector |||
    case_stmt ||| hasharrayaccesses
  )

  lazy val fstmt: P[Function] = (
    name ~ ("(" ~> expressions.? <~ ")") ^^ {
      case n ~ Some (es) => Function (n, es, Ftstmt)
      case n ~ None => Function (n, List[Expr] (), Ftstmt)
    }
  | name ~ ("(" ~> expressions <~ ",".? <~ ")") ^^ {
        case n ~ es => Function (n, es, Ftstmt)
      }
  | name ~ rep1sep (rvalue, ",") ^^ {
      case n ~ rvs => Function (n, rvs, Ftstmt)
    }
  )

  lazy val expressions: P[List[Expr]] = repsep (expr, ("," | "=>"))

  lazy val rvalue: P[Expr] = (
    selector |  array | hasharrayaccesses | resourceref | funcrvalue |
    undef | variable | quotedtext | boolean | name | asttype
  )

  lazy val resource: P[Resource] =
    classname ~ ("{" ~> resourceinstances <~ ";".? <~ "}") ^^ {
      case cn ~ ris => Resource (cn, ris)
    }

  lazy val resource_defaults: P[ResourceDefaults] =
    asttype ~ ("{" ~> params.? <~ ",".? <~ "}") ^^ {
      case t ~ None => ResourceDefaults (t, List ())
      case t ~ Some(params) => ResourceDefaults (t, params.map((p) => ReplaceAttribute(p.name, p.value)))
    }

  lazy val resourceoverride: P[ResourceOverride] =
    resourceref ~ ("{" ~> anyparams <~ ",".? <~ "}") ^^ {
      case rref ~ anyparams => ResourceOverride (rref, anyparams)
    }

  lazy val virtualresource: P[VirtualResource] = (
    "@" ~> resource ^^ (VirtualResource (_, Vrtvirtual))
  | "@@" ~> resource ^^ (VirtualResource (_, Vrtexported))
  )

  lazy val collection: P[Collection] = (
    asttype ~ collectrhand ~ ("{" ~> anyparams <~ ",".? <~ "}") ^^ {
      case t ~ collrhand ~ anyparams => Collection (t, collrhand._1, collrhand._2, anyparams)
    }
  | asttype ~ collectrhand ^^ {
      case t ~ collrhand => Collection (t, collrhand._1, collrhand._2, List[AttributeOverride] ())
    }
  )

  lazy val collectrhand: P[(Option[CollectionExpr], VirtualResType)] = (
    "<|" ~> collstmts.? <~ "|>" ^^ ((_, Vrtvirtual))
  | "<<|" ~> collstmts.? <~ "|>>" ^^ ((_, Vrtexported))
  )

  lazy val collstmts: P[CollectionExpr] = (
    collstmt
  | collstmts ~ ("and" | "or") ~ collstmt ^^ {
      case x ~ "and" ~ y => CollectionExpr (x, y, CollAnd)
      case x ~ "or"  ~ y => CollectionExpr (x, y, CollOr)
    }
  )

  lazy val collstmt: P[CollectionExpr] = collexpr | "(" ~> collstmts <~ ")"

  lazy val collexpr: P[CollectionExpr] =
    colllval ~ ("==" | "!=") ~ expr ^^ {
      case x ~ "==" ~ y => CollectionExpr (x, y, CollIsEq)
      case x ~ "!=" ~ y => CollectionExpr (x, y, CollNotEq)
    }

  lazy val colllval: P[CollectionExprOperand] = variable | name

  lazy val resourceinst: P[ResourceInstance] =
    resourcename ~ (":" ~> params.? <~ ",".?) ^^ {
      case resnm ~ None => ResourceInstance (resnm, List ())
      case resnm ~ Some (params) => ResourceInstance (resnm, params)
    }

  lazy val resourceinstances: P[List[ResourceInstance]] = repsep (resourceinst, ";")

  lazy val undef = "undef" ^^^ Undef

  lazy val default = "default" ^^^ Default

  lazy val name: P[Name] = NAMETOK ^^ (Name (_))

  lazy val asttype: P[Type] = CLASSREF ^^ (Type (_))

  lazy val resourcename: P[ResourceName] =
    selector | array | hasharrayaccesses | variable | quotedtext | name | asttype

  lazy val assignment: P[Vardef] = (
    hasharrayaccess ~ ("=" ~> expr) ^^ {
      case haa ~ e => Vardef (haa, e, false)
    }
  // TODO : A variable from another namespace cannot be assigned, see puppet parser
  | variable ~ ("=" ~> expr) ^^ {
      case vrbl ~ e => Vardef (vrbl, e, false)
    }
  )

  lazy val append: P[Vardef] =
    variable ~ ("+=" ~> expr) ^^ {
      case vrbl ~ e => Vardef (vrbl, e, true)
    }

  lazy val params: P[List[Attribute]] = (
    "," ~> rep1sep (param, ",") | repsep (param, ",")
  )

  lazy val param_name: P[AttributeNameType] = keyword ^^ (Name (_)) | name | boolean

  lazy val keyword: P[String] = "and" | "case" | "class" | "default" |
    "define" | "else" | "elsif" | "if" | "in" | "import" | "inherits" |
    "node" | "or" | "undef" | "unless"

  lazy val param: P[Attribute] =
    param_name ~ ("=>" ~> expr) ^^ {
      case pn ~ e => Attribute (pn, e)
    }

  lazy val addparam: P[AttributeOverride] =
    name ~ ("+>" ~> expr) ^^ {
      case name ~ e => AppendAttribute(name, e)
    }

  lazy val anyparams: P[List[AttributeOverride]] =
    repsep((param ^^ {case Attribute(n, e) => ReplaceAttribute(n,e)} | addparam), ",")

  lazy val funcrvalue: P[Function] =
      name ~ ("(" ~> (expressions.?) <~ ")") ^^ {
      case name ~ Some (es) => Function (name, es,           Ftrval)
      case name ~ None      => Function (name, List[Expr] (), Ftrval)
    }

  private def makeQuotedText(parts: List[String]): QuotedText = parts match {
    case part :: Nil => ASTString(part)
    case pre :: mid :: post => Concat(ASTString(pre),
                                      PuppetParser.interpExpr(mid.stripPrefix("${").stripSuffix("}")),
                                      makeQuotedText(post))
    case _ => throw new Exception("Error: invalid number of elements parsed while interpolating")
  }
    

  lazy val quotedtext: P[QuotedText] = (
    STRING ^^ (ASTString (_))
   | INTERPOLATION ^^ (makeQuotedText(_))
  // | INTERPOLATION ^^ {parts => ASTString(parts mkString "")}
  )

  lazy val boolean: P[ASTBool] =
    BOOLEAN ^^ {
      case "true" => ASTBool (true)
      case "false" => ASTBool (false)
    }

  lazy val resourceref: P[ResourceRef] = (
    /* TODO : Name production is deprecated and comes as a warning in original puppet parser
     *        It has to be a captitalized
     */
    name ~ ("[" ~> expressions <~ "]") ^^ {
      case name ~ es => ResourceRef (name, es)
    }
  | asttype ~ ("[" ~> expressions <~ "]") ^^ {
      case t ~ es => ResourceRef (t, es)
    }
  )

  // NOTE: Parser parses unless to IfStmt
  lazy val unless_stmt: P[IfStmt] =
    "unless" ~> expr ~ ("{" ~> stmt.* <~ "}") ^^ {
      case e ~ ss => IfStmt (NotExpr (e), ss, List ())
    }

  lazy val ifstmt : P[IfStmt] = {

    lazy val ifstmt_cont: P[IfStmt] =
      expr ~ ("{" ~> stmt.* <~ "}") ~ elsestmt.? ^^ {
        case e ~ ss ~ None      => IfStmt (e, ss, List ())
        case e ~ ss ~ Some (es) => IfStmt (e, ss, es)
      }

    lazy val elsestmt: P[List[Statement]] = (
      "elsif" ~> ifstmt_cont ^^ { case ifexp => List (ifexp) }
    | "else" ~> "{" ~> stmt.* <~ "}"
    )

    "if" ~> ifstmt_cont
  }

  private lazy val parens: P[Expr] = "(" ~> expr <~ ")"
  private lazy val uminus: P[Expr] = "-" ~> term ^^ (UMinusExpr (_))
  private lazy val not:    P[Expr] = "!" ~> term ^^ (NotExpr (_))
  private lazy val term:   P[Expr] = (rvalue | hash | parens | uminus | not | regex)

  private def binaryOp (level: Int): Parser[((Expr, Expr) => Expr)] = {
    level match {
      case 1 => "or"  ^^^ { (e1, e2) => BinExpr(e1, e2, Or)  }

      case 2 => "and" ^^^ { (e1, e2) => BinExpr(e1, e2, And) }

      case 3 =>
        ">"   ^^^ { (e1: Expr, e2: Expr) => BinExpr(e1, e2, GreaterThan) } |
        ">="  ^^^ { (e1: Expr, e2: Expr) => BinExpr(e1, e2, GreaterEq)   } |
        "<"   ^^^ { (e1: Expr, e2: Expr) => BinExpr(e1, e2, LessThan)    } |
        "<="  ^^^ { (e1: Expr, e2: Expr) => BinExpr(e1, e2, LessEq)      }

      case 4 =>
        "!=" ^^^ { (e1: Expr, e2: Expr) => BinExpr(e1, e2, NotEqual) } |
        "==" ^^^ { (e1: Expr, e2: Expr) => BinExpr(e1, e2, Equal)    }

      case 5 =>
        "<<" ^^^ { (e1: Expr, e2: Expr) => BinExpr(e1, e2, LShift) } |
        ">>" ^^^ { (e1: Expr, e2: Expr) => BinExpr(e1, e2, RShift) }

      case 6 =>
        "-" ^^^ { (e1: Expr, e2: Expr) => BinExpr(e1, e2, Minus) } |
        "+" ^^^ { (e1: Expr, e2: Expr) => BinExpr(e1, e2, Plus)  }

      case 7 =>
        "*" ^^^ { (e1: Expr, e2: Expr) => BinExpr(e1, e2, Mult) } |
        "/" ^^^ { (e1: Expr, e2: Expr) => BinExpr(e1, e2, Div)  } |
        "%" ^^^ { (e1: Expr, e2: Expr) => BinExpr(e1, e2, Mod)  }

      case 8 =>
        "in" ^^^ { (e1: Expr, e2: Expr) => BinExpr(e1, e2, In)      } |
        "=~" ^^^ { (e1: Expr, e2: Expr) => BinExpr(e1, e2, Match)   } |
        "!~" ^^^ { (e1: Expr, e2: Expr) => BinExpr(e1, e2, NoMatch) }

      case _ => throw new RuntimeException("bad precedence level " + level)
    }
  }

  private val minPrec = 1
  private val maxPrec = 8

  private def binary (level: Int): Parser[Expr] =
    if (level > maxPrec) term
    else binary(level+1) * binaryOp(level)

  lazy val expr: P[Expr] = (binary(minPrec) | term)

  lazy val case_stmt: P[CaseStmt] =
    "case" ~> expr ~ ("{" ~> caseopts <~ "}") ^^ {
      case e ~ csopts => CaseStmt (e, csopts)
    }

  lazy val caseopts: P[List[CaseOpt]] = (
    caseopt ^^ (List (_))
  ||| caseopts ~ caseopt ^^ {
      case cs ~ c => cs :+ c
    }
  )

  lazy val caseopt: P[CaseOpt] =
    casevalues ~ (":" ~> "{" ~> stmt.* <~ "}") ^^ { case csvs ~ ss => CaseOpt (csvs, ss) }

  lazy val casevalues: P[List[SelectLHS]] = repsep (selectlhand, ",")


  lazy val selector: P[Selector] =
    selectlhand ~ ("?" ~> svalues) ^^ {
      case slctlhnd ~ svals => Selector (slctlhnd, svals)
    }

  lazy val svalues: P[List[Attribute]] =
    (selectval ^^ (List (_))
  | "{" ~> sintvalues <~ ",".? <~ "}")

  lazy val sintvalues: P[List[Attribute]] = repsep(selectval, ("," | "=>"))

  lazy val selectval: P[Attribute] =
    selectlhand ~ ("=>" ~> rvalue) ^^ {
      case slcthnd ~ rval => Attribute(slcthnd, rval)
    }

  lazy val selectlhand: P[SelectLHS] = (
    funcrvalue | hasharrayaccess | boolean | undef | default |
    name | asttype | quotedtext | variable | regex
  )

  lazy val string: P[String] = STRING

  lazy val strings: P[List[String]] = repsep(string, ",")

  lazy val import_stmt: P[Import] =
    // TODO : Deprecated in puppet, Should show as warning
    "import" ~> strings ^^ (Import (_))

  lazy val definition: P[Definition] =
    "define" ~> classname ~ argumentlist.? ~ ("{" ~> stmt.* <~ "}") ^^ {
      case cnm ~ None        ~ ss => Definition(cnm, List (), ss)
      case cnm ~ Some (args) ~ ss => Definition(cnm, args, ss)
    }

  lazy val hostclass: P[Hostclass] =
    "class" ~> classname ~ argumentlist.? ~ classparent.? ~ ("{" ~> stmts_and_decls.? <~ "}") ^^ {
      case cnm ~ None        ~ clp ~ None      => Hostclass(cnm, List(), clp, BlockStmtDecls(List()))
      case cnm ~ None        ~ clp ~ Some (ss) => Hostclass(cnm, List(), clp, ss)
      case cnm ~ Some (args) ~ clp ~ None      => Hostclass(cnm, args, clp, BlockStmtDecls(List()))
      case cnm ~ Some (args) ~ clp ~ Some (ss) => Hostclass(cnm, args, clp, ss)
    }

  lazy val nodedef: P[Node] = (
    "node" ~> hostnames ~ nodeparent.? ~ ("{" ~> stmt.* <~ "}") ^^ {
      case hosts ~ ndp ~ ss => Node (hosts, ndp, ss)
    }
  )

  lazy val classname: P[String] = "class" | NAMETOK

  lazy val hostnames: P[List[Hostname]] = repsep (hostname, ",")

  lazy val hostname: P[Hostname] = ("default" ^^ (Name(_))) | name | STRING ^^ (ASTString(_)) | regex

  lazy val argumentlist: P[List[(Variable, Option[Expr])]] = (
    "(" ~> arguments.? <~ ")" ^^ {
      case None => List()
      case Some(ss) => ss
    }
  | "(" ~> arguments <~ ",".? <~ ")"
  )

  lazy val arguments: P[List[(Variable, Option[Expr])]] = repsep (argument, ",")

  lazy val argument: P[(Variable, Option[Expr])] = (
    variable ~ ("=" ~> expr) ^^ { case v ~ e => (v, Some (e)) }
  | variable ^^ ((_, None))
  )

  lazy val nodeparent: P[Hostname] = "inherits" ~> hostname

  lazy val classparent: P[String] = "inherits" ~> (classname | "default")

  lazy val variable: P[Variable] = VARIABLETOK ^^ (Variable (_))

  lazy val array: P[ASTArray] = (
    "[" ~> expressions.? <~ "]" ^^ {
      case None => ASTArray (List ())
      case Some (es) => ASTArray (es)
    }
  | "[" ~> expressions <~ "," <~ "]" ^^ (ASTArray (_))
  )

  lazy val regex: P[ASTRegex] = REGEXTOK ^^ (ASTRegex (_))

  lazy val hash: P[ASTHash] = (
    "{" ~> hashpairs.? <~ "}" ^^ {
      case None => ASTHash (List ())
      case Some (kvs) => ASTHash (kvs)
    }
  | "{" ~> hashpairs <~ "," <~ "}" ^^ (ASTHash (_))
  )

  lazy val hashpairs: P[List[(HashKey, Expr)]] = repsep (hashpair, ",")

  lazy val hashpair: P[(HashKey, Expr)] = key ~ ("=>" ~> expr) ^^ {
    case k ~ e => (k, e)
  }

  lazy val key: P[HashKey] = (name | quotedtext)

  lazy val hasharrayaccess: P[HashOrArrayAccess] =
    variable ~ ("[" ~> expr <~ "]") ^^ {
      case v ~ e => HashOrArrayAccess (v, e :: Nil)
    }

  lazy val hasharrayaccesses: P[HashOrArrayAccess] = (
    variable ~ ("[" ~> expr <~ "]").+ ^^ {
      case v ~ es => HashOrArrayAccess (v, es)
    }
  )

  import lexical.{PuppetBool, PuppetName, PuppetClassRef, PuppetRegex,
                  PuppetVariable, PuppetInterpolation}

  def STRING: Parser[String] = stringLit

  def BOOLEAN: Parser[String] =
    elem ("boolean", _.isInstanceOf[PuppetBool]) ^^ (_.chars)

  def NAMETOK: Parser[String] =
    elem ("name", _.isInstanceOf[PuppetName]) ^^ (_.chars)

  def CLASSREF: Parser[String] =
    elem ("classref", _.isInstanceOf[PuppetClassRef]) ^^ (_.chars)

  def REGEXTOK: Parser[String] =
    elem ("regex", _.isInstanceOf[PuppetRegex]) ^^ (_.chars)

  def VARIABLETOK: Parser[String] =
    elem ("variable", _.isInstanceOf[PuppetVariable]) ^^ (_.chars)

  def INTERPOLATION: Parser[List[String]] =
    elem ("interpolation", _.isInstanceOf[PuppetInterpolation]) ^^ (_.asInstanceOf[PuppetInterpolation].parts)

  private def parseExpr(s: String) = {
    val tokens = lexical.tokenize(s)
    
    /*
    println("----------")
    val tok = tokens.first
    println("IsKeyword: " + tok.isInstanceOf[lexical.Keyword])
    println("Length of keyword: " + tok.chars.length)
    println("Keyword chars: " + tok.chars)
    println("Keyword tostr: " + tok.toString)
    println("Test ---------------")
    println("Equality1: " + (lexical.Keyword("!") == tok))
    val res = tok.equals(lexical.Keyword("!"))
    println("Info tok: " +  tok.getClass.getName)
    println("Info keyword: " +  lexical.Keyword("!").getClass.getName)
    println("Equality4: " + (lexical.Keyword("!") == lexical.Keyword("!")))
    */

    phrase(expr)(tokens)
    // phrase(log(accept(lexical.Keyword("!")))("! parser") ^^ ((k) => ASTString(k.chars)))(tokens)
  }

  def parseAll(s: String) = {
    val tokens = lexical.tokenize(s)
    // Parses up to EOF, otherwise fails.
    phrase(program)(tokens)
  }
}

case class PuppetParserException(msg: String) extends Exception(msg)

object PuppetParser {

  private val programParser = new PuppetParser(new ProgramLexer)
  private val interpParser = new PuppetParser(new VariableLexer)
  private val proginterpParser = new PuppetParser(new ProgramLexer)

  def apply(in: String) : TopLevel = programParser.parseAll(in) match {
    case programParser.Success(ast, _) => ast
    case programParser.NoSuccess(msg, nxt) => throw PuppetParserException("Parsing failed: %s\n Rest of Input: %s".format(msg, nxt))
  }

  // If first token passes the interpolated variable test then make 'expr' parser see the first token as PuppetVariable
  /*private*/ def interpExpr(in: String): Expr = interpParser.parseExpr(in) match {
    case interpParser.Success(ast, _) => ast
    case interpParser.NoSuccess(msg, nxt) => throw PuppetParserException("Parsing failed: %s\n Rest of Input: %s".format(msg, nxt))
  }

  /*private*/ def interpExprPrg(in: String): Expr = proginterpParser.parseExpr(in) match {
    case proginterpParser.Success(ast, _) => ast
    case proginterpParser.NoSuccess(msg, nxt) => throw PuppetParserException("Parsing failed: %s\n Rest of Input: %s".format(msg, in))
  }

  def example(in: String) = {
    val lexer = new ProgramLexer
    var tokens = new lexer.Scanner(in)
    while (!tokens.atEnd) {
      println (tokens.first)
      println(tokens.pos)
      tokens = tokens.rest
    }
  }
}
