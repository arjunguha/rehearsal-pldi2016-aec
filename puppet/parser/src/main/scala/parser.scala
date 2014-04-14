/* Parser using parser combinator in Scala */

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
  | REGEX    ^^ (PuppetRegex (_))
  | VARIABLE ^^ (PuppetVariable (_))
  | '\'' ~ rep( chrExcept('\'', '\n', EofCh) ) ~ '\'' ^^ { 
      case '\'' ~ chars ~ '\'' => StringLit(chars mkString "")
    }
  |  '\"' ~ rep( chrExcept('\"', '\n', EofCh) ) ~ '\"' ^^ {
      case '\"' ~ chars ~ '\"' => StringLit(chars mkString "")
    }
  |  EofCh                                             ^^^ EOF
  |  '\'' ~> failure("unclosed string literal")
  |  '\"' ~> failure("unclosed string literal")
  |  delim
  |  failure("illegal character")
  )


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
  private def REGEX: Parser[String] = """/[^/\n]*/""".r

  private def VARIABLE: Parser[String] = ( 
    """\$(?:::)?(?:[-\w]+::)*[-\w]+""".r // DOLLAR_VAR_WITH_DASH
  | """\$(::)?(\w+::)*\w+""".r           // DOLLAR_VAR
  )

  // TODO : DQPRE, DQMID, DQPOST
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

  // TODO : See if we need EOF as a production here
  lazy val program: P[AST] =   stmts_and_decls 
                         /*    | (EofCh  ^^^ (BlockExpr (List[AST] ()))) */

  lazy val stmts_and_decls: P[BlockExpr] = stmt_or_decl.* ^^ (BlockExpr (_))

  lazy val stmt_or_decl: P[AST] = (
    resource ||| virtualresource ||| collection ||| assignment ||| case_stmt ||| 
    ifstmt_begin ||| unless_stmt ||| import_stmt ||| fstmt ||| definition |||
    hostclass ||| nodedef ||| resourceoverride ||| append ||| relationship
  )

  lazy val relationship: P[AST] = 
    relationship_side ~ (("<-" | "->" | "<~" | "~>") ~ relationship_side).+ ^^ { 
      case rs ~ rss => rss.foldLeft (rs) { 
          case (x, "<-" ~ y) => RelationExpr (x, y, LeftSimpleDep)
          case (x, "->" ~ y) => RelationExpr (x, y, RightSimpleDep)
          case (x, "<~" ~ y) => RelationExpr (x, y, LeftSubscribeDep)
          case (x, "~>" ~ y) => RelationExpr (x, y, RightSubscribeDep)
        }
      }

  lazy val relationship_side: P[AST] = (
    resource ||| resourceref ||| collection ||| variable ||| quotedtext ||| selector ||| 
    case_stmt ||| hasharrayaccesses
  )

  lazy val fstmt: P[Function] = (
    NAME ~ ("(" ~> expressions.? <~ ")") ^^ { 
      case n ~ Some (es) => Function (n, es, Ftstmt)
      case n ~ None => Function (n, List[AST] (), Ftstmt)
    }
  ||| NAME ~ ("(" ~> expressions <~ ",".? <~ ")") ^^ {
        case n ~ es => Function (n, es, Ftstmt)
      }
  ||| NAME ~ repsep (rvalue, ",") ^^ { 
      case n ~ rvs => Function (n, rvs, Ftstmt)
    }
  )

  lazy val expressions: P[List[AST]] = repsep (expr, ("," | "=>"))


  lazy val rvalue: P[AST] =
    quotedtext ||| name ||| asttype ||| boolean ||| selector ||| variable ||| array ||| hasharrayaccesses |||
    resourceref ||| funcrvalue ||| undef
    
  lazy val resource: P[AST] = (
    classname ~ ("{" ~> resourceinstances <~ ";".? <~ "}") ^^ {
      case cn ~ ris => Resource (cn, ris) 
    }
  ||| asttype ~ ("{" ~> params.? <~ ",".? <~ "}") ^^ {
      case t ~ None => ResourceDefaults (t, List ())
      case t ~ Some (params) => ResourceDefaults (t, params)
    }
  )

  lazy val resourceoverride: P[ResourceOverride] =
    resourceref ~ ("{" ~> anyparams <~ ",".? <~ "}") ^^ {
      case rref ~ anyparams => ResourceOverride (rref, anyparams)
    }

  lazy val virtualresource: P[VirtualResource] = (
    "@" ~> resource ^^ (VirtualResource (_, Vrtvirtual))
  ||| "@@" ~> resource ^^ (VirtualResource (_, Vrtexported))
  )

  lazy val collection: P[Collection] = (
    asttype ~ collectrhand ~ ("{" ~> anyparams <~ ",".? <~ "}") ^^ {
      case t ~ cltrhnd ~ anyparams => Collection (t, cltrhnd, anyparams)
    }
  ||| asttype ~ collectrhand ^^ { 
      case t ~ cltrhnd => Collection (t, cltrhnd, List[ResourceParam] ())
    }
  )

  lazy val collectrhand: P[CollectionExprTagNode] = (
    "<|" ~> collstmts.? <~ "|>" ^^ (CollectionExprTagNode (_, Vrtvirtual))
  ||| "<<|" ~> collstmts.? <~ "|>>" ^^ (CollectionExprTagNode (_, Vrtexported))
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

  lazy val colllval: P[AST] = variable | name

  lazy val resourceinst: P[ResourceInstance] = 
    resourcename ~ (":" ~> params.? <~ ",".?) ^^ {
      case resnm ~ None => ResourceInstance (resnm, List ())
      case resnm ~ Some (params) => ResourceInstance (resnm, params)
    }

  lazy val resourceinstances: P[List[ResourceInstance]] = repsep (resourceinst, ";")

  lazy val undef: P[AST] = "undef" ^^^ Undef

  lazy val name: P[Name] = NAME ^^ (Name (_))

  lazy val asttype: P[Type] = CLASSREF ^^ (Type (_))

  lazy val resourcename: P[AST] =
    quotedtext ||| name ||| asttype ||| selector ||| variable ||| array ||| hasharrayaccesses

  lazy val assignment: P[Vardef] = (
    VARIABLE ~ ("=" ~> expr) ^^ { 
      case vrbl ~ e => Vardef (Name (vrbl), e, false)
    }
  ||| hasharrayaccess ~ ("=" ~> expr) ^^ { 
      case haa ~ e => Vardef (haa, e, false)
    }
  )

  lazy val append: P[Vardef] = 
    VARIABLE ~ ("+=" ~> expr) ^^ {
      case vrbl ~ e => Vardef (Name (vrbl), e, true)
    }

  lazy val params: P[List[ResourceParam]] = repsep (param, ",")

  lazy val param_name: P[AST] = name | keyword ^^ (ASTString (_)) | boolean

  lazy val keyword: P[String] = "and" | "case" | "class" | "default" |
    "define" | "else" | "elsif" | "if" | "in" | "import" | "inherits" |
    "node" | "or" | "undef" | "unless"

  lazy val param: P[ResourceParam] = 
    param_name ~ ("=>" ~> expr) ^^ {
      case pn ~ e => ResourceParam (pn, e, false)
    }

  lazy val addparam: P[ResourceParam] = 
    name ~ ("+>" ~> expr) ^^ {
      case name ~ e => ResourceParam (name, e, true)
    }

  lazy val anyparams: P[List[ResourceParam]] = repsep ((param | addparam), ",")

  lazy val funcrvalue: P[Function] = 
    NAME ~ ("(" ~> expressions.? <~ ")") ^^ {
      case name ~ Some (es) => Function (name, es,           Ftrval)
      case name ~ None      => Function (name, List[AST] (), Ftrval)
    }

  lazy val quotedtext: P[AST] = STRING ^^ (ASTString (_))
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
    name ~ ("[" ~> expressions <~ "]") ^^ {
      case name ~ es => ResourceRef (name, es)
    }
  ||| asttype ~ ("[" ~> expressions <~ "]") ^^ {
      case t ~ es => ResourceRef (t, es)
    }
  )

  // TODO: stmts_and_decls can return "nothing", do we really need to "repeat" ourself
  //      with ".?"
  lazy val unless_stmt: P[IfExpr] =
    "unless" ~> expr ~ ("{" ~> stmts_and_decls.? <~ "}") ^^ {
      case e ~ Some (ss) => IfExpr (NotExpr (e), ss,                  BlockExpr (List ()))
      case e ~ None      => IfExpr (NotExpr (e), BlockExpr (List ()), BlockExpr (List ()))
    }

  lazy val ifstmt_begin: P[IfExpr] = "if" ~> ifstmt

  lazy val ifstmt: P[IfExpr] = 
    expr ~ ("{" ~> stmts_and_decls.? <~ "}") ~ elsestmt.? ^^ {
      case e ~ None      ~ None      => IfExpr (e, BlockExpr (List ()), BlockExpr (List ()))
      case e ~ Some (ss) ~ None      => IfExpr (e, ss,                  BlockExpr (List ()))
      case e ~ None      ~ Some (es) => IfExpr (e, BlockExpr (List ()), es)
      case e ~ Some (ss) ~ Some (es) => IfExpr (e, ss, es)
    }

  // TODO: stmts_and_decls can return "nothing", do we really need to "repeat" ourself
  //      with ".?"
  lazy val elsestmt: P[BlockExpr] = (
    "elsif" ~> ifstmt ^^ { 
      case ifexp => BlockExpr (List (ifexp))
    }
  ||| "else" ~> "{" ~> stmts_and_decls.? <~ "}" ^^ {
      case None => BlockExpr (List ())
      case Some (ss) => ss
    }
  )

  private lazy val parens: P[AST] = "(" ~> expr <~ ")"
  private lazy val uminus: P[AST] = "-" ~> expr ^^ (UMinusExpr (_))
  private lazy val not:    P[AST] = "!" ~> expr ^^ (NotExpr (_))
  private lazy val term:   P[AST] = (rvalue | hash | parens | uminus | not | regex_stmt)


  private def binaryOp (level: Int): Parser[((AST, AST) => AST)] = {
    level match {
      case 1 => "or"  ^^^ { (e1, e2) => BinExpr (e1, e2, Or)  }

      case 2 => "and" ^^^ { (e1, e2) => BinExpr (e1, e2, And) }

      case 3 => 
        ">"   ^^^ { (e1: AST, e2: AST) => BinExpr (e1, e2, GreaterThan) } |
        ">="  ^^^ { (e1: AST, e2: AST) => BinExpr (e1, e2, GreaterEq)   } |
        "<"   ^^^ { (e1: AST, e2: AST) => BinExpr (e1, e2, LessThan)    } |
        "<="  ^^^ { (e1: AST, e2: AST) => BinExpr (e1, e2, LessEq)      }

      case 4 =>
        "!=" ^^^ { (e1: AST, e2: AST) => BinExpr (e1, e2, NotEqual) } |
        "==" ^^^ { (e1: AST, e2: AST) => BinExpr (e1, e2, Equal)    }
        
      case 5 =>
        "<<" ^^^ { (e1: AST, e2: AST) => BinExpr (e1, e2, LShift) } |
        ">>" ^^^ { (e1: AST, e2: AST) => BinExpr (e1, e2, RShift) } 

      case 6 =>
        "-" ^^^ { (e1: AST, e2: AST) => BinExpr (e1, e2, Minus) } |
        "+" ^^^ { (e1: AST, e2: AST) => BinExpr (e1, e2, Plus)  }

      case 7 =>
        "*" ^^^ { (e1: AST, e2: AST) => BinExpr (e1, e2, Mult) } |
        "/" ^^^ { (e1: AST, e2: AST) => BinExpr (e1, e2, Div)  } |
        "%" ^^^ { (e1: AST, e2: AST) => BinExpr (e1, e2, Mod)  }
        
      case 8 =>
        "in" ^^^ { (e1: AST, e2: AST) => BinExpr (e1, e2, In)      } |
        "=~" ^^^ { (e1: AST, e2: AST) => BinExpr (e1, e2, Match)   } |
        "!~" ^^^ { (e1: AST, e2: AST) => BinExpr (e1, e2, NoMatch) }

      case _ => throw new RuntimeException ("bad precedence level " + level)
    }
  }

  private val minPrec = 1
  private val maxPrec = 8

  private def binary (level: Int): Parser[AST] =
    if (level > maxPrec) term
    else binary (level + 1) * binaryOp (level)

  lazy val expr: P[AST] = (binary (minPrec) | term)

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

  // TODO: stmts_and_decls can return "nothing", do we really need to "repeat" ourself
  //      with ".?"
  lazy val caseopt: P[CaseOpt] =
    casevalues ~ (":" ~> "{" ~> stmts_and_decls.? <~ "}") ^^ {
      case csvs ~ None => CaseOpt (csvs, BlockExpr (List ()))
      case csvs ~ Some (ss) => CaseOpt (csvs, ss)
    }

  lazy val casevalues: P[List[AST]] = repsep (selectlhand, ",")


  lazy val selector: P[Selector] =
    selectlhand ~ ("?" ~> svalues) ^^ {
      case slctlhnd ~ svals => Selector (slctlhnd, svals)
    }

  lazy val svalues: P[List[ResourceParam]] = 
    (selectval ^^ (List (_))
  ||| "{" ~> sintvalues <~ ",".? <~ "}")

  lazy val sintvalues: P[List[ResourceParam]] = repsep (selectval, ("," | "=>"))

  lazy val selectval: P[ResourceParam] =
    selectlhand ~ ("=>" ~> rvalue) ^^ {
      case slcthnd ~ rval => ResourceParam (slcthnd, rval, false)
    }

  lazy val selectlhand: P[AST] = (
    name ||| asttype ||| quotedtext ||| variable ||| funcrvalue ||| boolean ||| undef |||
    hasharrayaccess ||| ("default" ^^^ Default) ||| regex_stmt
  )
    
  lazy val string: P[String] = STRING

  lazy val strings: P[List[String]] = repsep (string, ",") 

  lazy val import_stmt: P[Import] = 
    "import" ~> strings ^^ (Import (_))

  lazy val definition: P[Definition] = 
    "define" ~> classname ~ argumentlist.? ~ ("{" ~> stmts_and_decls.? <~ "}") ^^ {
      case cnm ~ None        ~ None      => Definition (cnm, List (), BlockExpr (List ()))
      case cnm ~ None        ~ Some (ss) => Definition (cnm, List (), ss)
      case cnm ~ Some (args) ~ None      => Definition (cnm, args, BlockExpr (List ()))
      case cnm ~ Some (args) ~ Some (ss) => Definition (cnm, args, ss)
    }

  lazy val hostclass: P[Hostclass] = 
    "class" ~> classname ~ argumentlist.? ~ classparent.? ~ ("{" ~> stmts_and_decls.? <~ "}") ^^ {
      case cnm ~ None        ~ clp ~ None      => Hostclass (cnm, List (), clp, BlockExpr (List ()))
      case cnm ~ None        ~ clp ~ Some (ss) => Hostclass (cnm, List (), clp, ss)
      case cnm ~ Some (args) ~ clp ~ None      => Hostclass (cnm, args, clp, BlockExpr (List ()))
      case cnm ~ Some (args) ~ clp ~ Some (ss) => Hostclass (cnm, args, clp, ss)
    }

  lazy val nodedef: P[Node] = (
    "node" ~> hostnames ~ nodeparent.? ~ ("{" ~> stmts_and_decls.? <~ "}") ^^ {
      case hosts ~ ndp ~ None => Node (hosts, ndp, BlockExpr (List ()))
      case hosts ~ ndp ~ Some (ss) => Node (hosts, ndp, ss)
    }
  )

  lazy val classname: P[String] = "class" | NAME

  lazy val hostnames: P[List[Hostname]] = repsep (nodename, ",") 

  lazy val nodename: P[Hostname] = hostname ^^ (Hostname (_))

  lazy val hostname: P[String] = "default" | NAME | STRING | REGEX

  lazy val argumentlist: P[List[(String, Option[AST])]] = (
    "(" ~> arguments.? <~ ")" ^^ {
      case None => List ()
      case Some (ss) => ss
    }
  ||| "(" ~> arguments <~ ",".? <~ ")"
  )

  lazy val arguments: P[List[(String, Option[AST])]] = repsep (argument, ",")

  lazy val argument: P[(String, Option[AST])] = (
    VARIABLE ~ ("=" ~> expr) ^^ { case v ~ e => (v, Some (e)) }
  ||| VARIABLE ^^ ((_, None))
  )

  lazy val nodeparent: P[String] = "inherits" ~> hostname

  lazy val classparent: P[String] = "inherits" ~> (classname | "default")

  lazy val variable: P[Variable] = VARIABLE ^^ (Variable (_))

  lazy val array: P[ASTArray] = (
    "[" ~> expressions.? <~ "]" ^^ {
      case None => ASTArray (List ())
      case Some (es) => ASTArray (es)
    }
  ||| "[" ~> expressions <~ "," <~ "]" ^^ (ASTArray (_))
  )

  lazy val regex_stmt: P[ASTRegex] = REGEX ^^ (ASTRegex (_))

  lazy val hash: P[ASTHash] = (
    "{" ~> hashpairs.? <~ "}" ^^ {
      case None => ASTHash (List ())
      case Some (kvs) => ASTHash (kvs)
    }
  ||| "{" ~> hashpairs <~ "," <~ "}" ^^ (ASTHash (_))
  )

  lazy val hashpairs: P[List[(AST, AST)]] = repsep (hashpair, ",")

  lazy val hashpair: P[(AST, AST)] = key ~ ("=>" ~> expr) ^^ {
    case k ~ e => (k, e)
  }

  lazy val key: P[AST] = (name | quotedtext)

  lazy val hasharrayaccess: P[HashOrArrayAccess] =
    variable ~ ("[" ~> expr <~ "]") ^^ {
      case v ~ e => HashOrArrayAccess (v, e)
    }

  lazy val hasharrayaccesses: P[HashOrArrayAccess] = (
    hasharrayaccess 
  ||| hasharrayaccesses ~ ("[" ~> expr <~ "]") ^^ {
      case haa ~ e => HashOrArrayAccess (haa, e)
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

  def REGEX: Parser[String] =
    elem ("regex", _.isInstanceOf[PuppetRegex]) ^^ (_.chars)

  def VARIABLE: Parser[String] =
    elem ("classref", _.isInstanceOf[PuppetVariable]) ^^ (_.chars)



  def parseAll (s: String) = {
    val tokens  = new lexical.Scanner (s)
    phrase (program)(tokens)
  }
}


object PuppetParser extends PuppetParser {

  def apply (in: String) = parseAll (in)
}
