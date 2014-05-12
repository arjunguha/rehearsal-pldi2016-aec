package puppet;

import scala.util.parsing.combinator._
import scala.util.parsing.combinator.syntactical._
import scala.util.parsing.combinator.lexical._
import scala.util.parsing.combinator.token._
import scala.util.parsing.input.CharArrayReader.EofCh


trait PuppetTokens extends StdTokens {

  case class PuppetBool (chars: String) extends Token {
    override def toString = "'"+chars+"'"
  }

  case class PuppetName (chars: String) extends Token {
    override def toString = chars
  }

  case class PuppetClassRef (chars: String) extends Token {
    override def toString = chars
  }

  case class PuppetRegex (chars: String) extends Token {
    override def toString = chars
  }

  case class PuppetVariable (chars: String) extends Token {
    override def toString = chars
  }
}

class PuppetLexical extends StdLexical 
                    with RegexParsers
                    with PuppetTokens {

  override type Elem = Char

  override def token: Parser[Token] = (
    NAME ^^ (processName (_))
  | CLASSREF ^^ (PuppetClassRef (_))
  | REGEXTOK    ^^ (PuppetRegex (_))
  | VARIABLETOK ^^ (PuppetVariable (_))
  | '\'' ~ stringlit ('\'') ~ '\'' ^^ { case '\'' ~ chars ~ '\'' => StringLit ("\'" +  chars + "\'") }
  |  '\"' ~ stringlit ('\"') ~ '\"' ^^ { case '\"' ~ chars ~ '\"' => StringLit ("\"" + chars + "\"") }
  |  EofCh ^^^ EOF
  |  '\'' ~> failure("unclosed string literal")
  |  '\"' ~> failure("unclosed string literal")
  |  delim
  |  failure("illegal character")
  )

  private def stringlit (quote_char: Char): Parser[String] = (
    rep (chrExcept ('\\', quote_char))  ~ escape_seq ~ stringlit (quote_char) ^^ { case chars ~ es ~ strlit => (chars mkString "") + es + strlit }
  | rep (chrExcept ('\\', quote_char, EofCh)) ^^ (_ mkString "")
  )

  private def escape_seq: Parser[String] = '\\' ~ chrExcept (EofCh) ^^ { case '\\' ~ ch => "\\" + ch }

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

  private def BOOLEAN: Parser[String] = ("true" | "false")

  private def NAME: Parser[String] = ("""((::)?[a-z0-9][-\w]*)(::[a-z0-9][-\w]*)*""".r
                           ||| NUMBER)

  private def NUMBER:Parser[String] = """\b(?:0[xX][0-9A-Fa-f]+|0?\d+(?:\.\d+)?(?:[eE]-?\d+)?)\b""".r

  private def CLASSREF: Parser[String] = """((::){0,1}[A-Z][-\w]*)+""".r

  // TODO : We might need to escape end of regex, See puppet lexer
  private def REGEXTOK: Parser[String] = """/[^/\n]*/""".r

  private def VARIABLETOK: Parser[String] = ( 
    """\$(?:::)?(?:[-\w]+::)*[-\w]+""".r // DOLLAR_VAR_WITH_DASH
  | """\$(::)?(\w+::)*\w+""".r           // DOLLAR_VAR
  )

  // TODO : DQPRE, DQMID, DQPOST or String Interpolation
}

class PuppetParser extends StdTokenParsers
                   with PackratParsers {

  type Tokens = PuppetTokens
  override val lexical = new PuppetLexical
  lexical.delimiters ++= List ("<-", "->", "<~", "~>",
                               "(", ")", "{", "}", "[", "]",
                               ",", ";", ":", ".",
                               "@@", "@", "<|", "|>", "<<|", "|>>",
                               "=>", "==", "!=", "=", "+=", "+>", "!", "=~", "!~", "?",
                               "+", "-", "/", "*", "%", "<<", ">>", ">", "<", ">=", "<=") 

  lexical.reserved ++= List ("and" , "case" , "class" , "default" ,
    "define" , "else" , "elsif" , "if" , "in" , "import" , "inherits" ,
    "node" , "or" , "undef" , "unless")
                               
  type P[+T] = PackratParser[T]

  // TODO : See if we need EOF as a production here || Check with empty manifest
  lazy val program: P[AST] =   stmts_and_decls 
                         /*    | (EofCh  ^^^ (BlockExpr (List[AST] ()))) */

  lazy val stmts_and_decls: P[BlockStmtDecls] = stmt_or_decl.* ^^ (BlockStmtDecls (_))

  lazy val stmt_or_decl: P[StmtOrDecl] = (stmt | decl)

  lazy val decl: P[TopLevelConstruct] = (definition | hostclass | nodedef)

  lazy val stmt: P[Statement] = (
    resource ||| virtualresource ||| collection ||| assignment ||| case_stmt ||| 
    ifstmt_begin ||| unless_stmt ||| import_stmt ||| fstmt ||| resourceoverride |||
    append ||| relationship
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
    resource ||| resourceref ||| collection ||| variable ||| quotedtext ||| selector ||| 
    case_stmt ||| hasharrayaccesses
  )

  lazy val fstmt: P[Function] = (
    name ~ ("(" ~> expressions.? <~ ")") ^^ { 
      case n ~ Some (es) => Function (n, es, Ftstmt)
      case n ~ None => Function (n, List[Expr] (), Ftstmt)
    }
  ||| name ~ ("(" ~> expressions <~ ",".? <~ ")") ^^ {
        case n ~ es => Function (n, es, Ftstmt)
      }
  ||| name ~ repsep (rvalue, ",") ^^ { 
      case n ~ rvs => Function (n, rvs, Ftstmt)
    }
  )

  lazy val expressions: P[List[Expr]] = repsep (expr, ("," | "=>"))

  lazy val rvalue: P[RValue] =
    quotedtext ||| name ||| asttype ||| boolean ||| selector ||| variable ||| 
    array ||| hasharrayaccesses ||| resourceref ||| funcrvalue ||| undef
    
  lazy val resource = ( resource_from_instance | resource_from_defaults )

  lazy val resource_from_instance: P[Resource] =
    classname ~ ("{" ~> resourceinstances <~ ";".? <~ "}") ^^ {
      case cn ~ ris => Resource (cn, ris) 
    }

  lazy val resource_from_defaults: P[ResourceDefaults] = 
    asttype ~ ("{" ~> params.? <~ ",".? <~ "}") ^^ {
      case t ~ None => ResourceDefaults (t, List ())
      case t ~ Some (params) => ResourceDefaults (t, params)
    }

  lazy val resourceoverride: P[ResourceOverride] =
    resourceref ~ ("{" ~> anyparams <~ ",".? <~ "}") ^^ {
      case rref ~ anyparams => ResourceOverride (rref, anyparams)
    }

  lazy val virtualresource: P[VirtualResource] = (
    "@" ~> resource_from_instance ^^ (VirtualResource (_, Vrtvirtual))
  ||| "@@" ~> resource_from_instance ^^ (VirtualResource (_, Vrtexported))
  )

  lazy val collection: P[Collection] = (
    asttype ~ collectrhand ~ ("{" ~> anyparams <~ ",".? <~ "}") ^^ {
      case t ~ collrhand ~ anyparams => Collection (t, collrhand._1, collrhand._2, anyparams)
    }
  ||| asttype ~ collectrhand ^^ { 
      case t ~ collrhand => Collection (t, collrhand._1, collrhand._2, List[Attribute] ())
    }
  )

  lazy val collectrhand: P[(Option[CollectionExpr], VirtualResType)] = (
    "<|" ~> collstmts.? <~ "|>" ^^ ((_, Vrtvirtual))
  ||| "<<|" ~> collstmts.? <~ "|>>" ^^ ((_, Vrtexported))
  )

  lazy val collstmts: P[CollectionExpr] = (
    collstmt
  | collstmts ~ ("and" | "or") ~ collstmt ^^ {
      case x ~ "and" ~ y => CollectionExpr (x, y, CollAnd)
      case x ~ "or"  ~ y => CollectionExpr (x, y, CollOr)
    }
  )

  lazy val collstmt: P[CollectionExpr] = collexpr ||| "(" ~> collstmts <~ ")"

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

  lazy val name: P[Name] = NAME ^^ (Name (_))

  lazy val asttype: P[Type] = CLASSREF ^^ (Type (_))

  lazy val resourcename: P[ResourceName] =
    quotedtext ||| name ||| asttype ||| selector ||| variable ||| array ||| hasharrayaccesses

  lazy val assignment: P[Vardef] = (
    // TODO : A variable from another namespace cannot be assigned, see puppet parser
    variable ~ ("=" ~> expr) ^^ { 
      case vrbl ~ e => Vardef (vrbl, e, false)
    }
  ||| hasharrayaccess ~ ("=" ~> expr) ^^ { 
      case haa ~ e => Vardef (haa, e, false)
    }
  )

  lazy val append: P[Vardef] = 
    variable ~ ("+=" ~> expr) ^^ {
      case vrbl ~ e => Vardef (vrbl, e, true)
    }

  lazy val params: P[List[Attribute]] = repsep (param, ",")

  lazy val param_name: P[AttributeNameType] = keyword ^^ (Name (_)) | name | boolean

  lazy val keyword: P[String] = "and" | "case" | "class" | "default" |
    "define" | "else" | "elsif" | "if" | "in" | "import" | "inherits" |
    "node" | "or" | "undef" | "unless"

  lazy val param: P[Attribute] = 
    param_name ~ ("=>" ~> expr) ^^ {
      case pn ~ e => Attribute (pn, e, false)
    }

  lazy val addparam: P[Attribute] = 
    name ~ ("+>" ~> expr) ^^ {
      case name ~ e => Attribute (name, e, true)
    }

  lazy val anyparams: P[List[Attribute]] = repsep ((param | addparam), ",")

  lazy val funcrvalue: P[Function] = 
      name ~ ("(" ~> expressions.? <~ ")") ^^ {
      case name ~ Some (es) => Function (name, es,           Ftrval)
      case name ~ None      => Function (name, List[Expr] (), Ftrval)
    }

  lazy val quotedtext: P[ASTString] = STRING ^^ (ASTString (_))
  /*
  | DQPRE ~ dqrval ^^ {
      case x ~ y => Concat (x, y)
    }
  */

  /*
  lazy val dqrval: P[List[AST]] =
    expr ~ dqtail ^^ {
      case e ~ y => e :: y
    }

  lazy val dqtail: P[List[AST]] = (
    DQPOST ^^ (List[ASTString] (ASTString (_)))
  | DQMID ~ dqrval ^^ {
      case x ~ y => x :: y
    }
  )
  */

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
  ||| asttype ~ ("[" ~> expressions <~ "]") ^^ {
      case t ~ es => ResourceRef (t, es)
    }
  )

  lazy val unless_stmt: P[IfExpr] =
    "unless" ~> expr ~ ("{" ~> stmt.* <~ "}") ^^ {
      case e ~ ss => IfExpr (NotExpr (e), ss, List ())
    }

  lazy val ifstmt_begin: P[IfExpr] = "if" ~> ifstmt

  lazy val ifstmt: P[IfExpr] = 
    expr ~ ("{" ~> stmt.* <~ "}") ~ elsestmt.? ^^ {
      case e ~ ss ~ None      => IfExpr (e, ss, List ())
      case e ~ ss ~ Some (es) => IfExpr (e, ss, es)
    }

  lazy val elsestmt: P[List[Statement]] = (
    "elsif" ~> ifstmt ^^ { case ifexp => List (ifexp) }
  ||| "else" ~> "{" ~> stmt.* <~ "}"
  )

  private lazy val parens: P[Expr] = "(" ~> expr <~ ")"
  private lazy val uminus: P[Expr] = "-" ~> expr ^^ (UMinusExpr (_))
  private lazy val not:    P[Expr] = "!" ~> expr ^^ (NotExpr (_))
  private lazy val term:   P[Expr] = (rvalue | hash | parens | uminus | not | regex)

  private def binaryOp (level: Int): Parser[((Expr, Expr) => Expr)] = {
    level match {
      case 1 => "or"  ^^^ { (e1, e2) => BinExpr (e1, e2, Or)  }

      case 2 => "and" ^^^ { (e1, e2) => BinExpr (e1, e2, And) }

      case 3 => 
        ">"   ^^^ { (e1: Expr, e2: Expr) => BinExpr (e1, e2, GreaterThan) } |
        ">="  ^^^ { (e1: Expr, e2: Expr) => BinExpr (e1, e2, GreaterEq)   } |
        "<"   ^^^ { (e1: Expr, e2: Expr) => BinExpr (e1, e2, LessThan)    } |
        "<="  ^^^ { (e1: Expr, e2: Expr) => BinExpr (e1, e2, LessEq)      }

      case 4 =>
        "!=" ^^^ { (e1: Expr, e2: Expr) => BinExpr (e1, e2, NotEqual) } |
        "==" ^^^ { (e1: Expr, e2: Expr) => BinExpr (e1, e2, Equal)    }
        
      case 5 =>
        "<<" ^^^ { (e1: Expr, e2: Expr) => BinExpr (e1, e2, LShift) } |
        ">>" ^^^ { (e1: Expr, e2: Expr) => BinExpr (e1, e2, RShift) } 

      case 6 =>
        "-" ^^^ { (e1: Expr, e2: Expr) => BinExpr (e1, e2, Minus) } |
        "+" ^^^ { (e1: Expr, e2: Expr) => BinExpr (e1, e2, Plus)  }

      case 7 =>
        "*" ^^^ { (e1: Expr, e2: Expr) => BinExpr (e1, e2, Mult) } |
        "/" ^^^ { (e1: Expr, e2: Expr) => BinExpr (e1, e2, Div)  } |
        "%" ^^^ { (e1: Expr, e2: Expr) => BinExpr (e1, e2, Mod)  }
        
      case 8 =>
        "in" ^^^ { (e1: Expr, e2: Expr) => BinExpr (e1, e2, In)      } |
        "=~" ^^^ { (e1: Expr, e2: Expr) => BinExpr (e1, e2, Match)   } |
        "!~" ^^^ { (e1: Expr, e2: Expr) => BinExpr (e1, e2, NoMatch) }

      case _ => throw new RuntimeException ("bad precedence level " + level)
    }
  }

  private val minPrec = 1
  private val maxPrec = 8

  private def binary (level: Int): Parser[Expr] =
    if (level > maxPrec) term
    else binary (level + 1) * binaryOp (level)

  lazy val expr: P[Expr] = (binary (minPrec) | term)

  lazy val case_stmt: P[CaseExpr] = 
    "case" ~> expr ~ ("{" ~> caseopts <~ "}") ^^ {
      case e ~ csopts => CaseExpr (e, csopts)
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
  ||| "{" ~> sintvalues <~ ",".? <~ "}")

  lazy val sintvalues: P[List[Attribute]] = repsep (selectval, ("," | "=>"))

  lazy val selectval: P[Attribute] =
    selectlhand ~ ("=>" ~> rvalue) ^^ {
      case slcthnd ~ rval => Attribute (slcthnd, rval, false)
    }

  lazy val selectlhand: P[SelectLHS] = (
    name ||| asttype ||| quotedtext ||| variable ||| funcrvalue |||
    boolean ||| undef ||| hasharrayaccess ||| default ||| regex
  )
    
  lazy val string: P[String] = STRING

  lazy val strings: P[List[String]] = repsep (string, ",") 

  lazy val import_stmt: P[Import] = 
    // TODO : Deprecated in puppet, Should show as warning
    // Consider saving quotes
    "import" ~> strings ^^ (Import (_))

  lazy val definition: P[Definition] = 
    "define" ~> classname ~ argumentlist.? ~ ("{" ~> stmt.* <~ "}") ^^ {
      case cnm ~ None        ~ ss => Definition (cnm, List (), ss)
      case cnm ~ Some (args) ~ ss => Definition (cnm, args, ss)
    }

  lazy val hostclass: P[Hostclass] = 
    "class" ~> classname ~ argumentlist.? ~ classparent.? ~ ("{" ~> stmts_and_decls.? <~ "}") ^^ {
      case cnm ~ None        ~ clp ~ None      => Hostclass (cnm, List (), clp, BlockStmtDecls (List ()))
      case cnm ~ None        ~ clp ~ Some (ss) => Hostclass (cnm, List (), clp, ss)
      case cnm ~ Some (args) ~ clp ~ None      => Hostclass (cnm, args, clp, BlockStmtDecls (List ()))
      case cnm ~ Some (args) ~ clp ~ Some (ss) => Hostclass (cnm, args, clp, ss)
    }

  lazy val nodedef: P[Node] = (
    "node" ~> hostnames ~ nodeparent.? ~ ("{" ~> stmt.* <~ "}") ^^ {
      case hosts ~ ndp ~ ss => Node (hosts, ndp, ss)
    }
  )

  lazy val classname: P[String] = "class" | NAME

  lazy val hostnames: P[List[Hostname]] = repsep (hostname, ",") 

  lazy val hostname: P[Hostname] = ("default" ^^ (Name (_))) | name | quotedtext | regex

  lazy val argumentlist: P[List[(Variable, Option[Expr])]] = (
    "(" ~> arguments.? <~ ")" ^^ {
      case None => List ()
      case Some (ss) => ss
    }
  ||| "(" ~> arguments <~ ",".? <~ ")"
  )

  lazy val arguments: P[List[(Variable, Option[Expr])]] = repsep (argument, ",")

  lazy val argument: P[(Variable, Option[Expr])] = (
    variable ~ ("=" ~> expr) ^^ { case v ~ e => (v, Some (e)) }
  ||| variable ^^ ((_, None))
  )

  lazy val nodeparent: P[Hostname] = "inherits" ~> hostname

  lazy val classparent: P[String] = "inherits" ~> (classname | "default")

  lazy val variable: P[Variable] = VARIABLETOK ^^ (Variable (_))

  lazy val array: P[ASTArray] = (
    "[" ~> expressions.? <~ "]" ^^ {
      case None => ASTArray (List ())
      case Some (es) => ASTArray (es)
    }
  ||| "[" ~> expressions <~ "," <~ "]" ^^ (ASTArray (_))
  )

  lazy val regex: P[ASTRegex] = REGEXTOK ^^ (ASTRegex (_))

  lazy val hash: P[ASTHash] = (
    "{" ~> hashpairs.? <~ "}" ^^ {
      case None => ASTHash (List ())
      case Some (kvs) => ASTHash (kvs)
    }
  ||| "{" ~> hashpairs <~ "," <~ "}" ^^ (ASTHash (_))
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

  import lexical.{PuppetBool, PuppetName, PuppetClassRef, PuppetRegex, PuppetVariable}

  def STRING: Parser[String] = stringLit

  def BOOLEAN: Parser[String] =
    elem ("boolean", _.isInstanceOf[PuppetBool]) ^^ (_.chars)

  def NAME: Parser[String] =
    elem ("name", _.isInstanceOf[PuppetName]) ^^ (_.chars)

  def CLASSREF: Parser[String] =
    elem ("classref", _.isInstanceOf[PuppetClassRef]) ^^ (_.chars)

  def REGEXTOK: Parser[String] =
    elem ("regex", _.isInstanceOf[PuppetRegex]) ^^ (_.chars)

  def VARIABLETOK: Parser[String] =
    elem ("classref", _.isInstanceOf[PuppetVariable]) ^^ (_.chars)

  def parseAll (s: String) = {
    val tokens  = new lexical.Scanner (s)
    phrase (program)(tokens)
  }
}

case class PuppetParserException (msg: String) extends Exception (msg);
  
object PuppetParser extends PuppetParser {

  def apply (in: String) = parseAll (in) match {
    case Success (ast, _) => ast
    case NoSuccess (msg, next) => throw PuppetParserException ("Parsing failed: %s\n Rest of Input: %s".format (msg, next))
  }
}
