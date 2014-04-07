/* Parser using parser combinator in Scala */

import scala.util.parsing.combinator._
import scala.util.parsing.combinator.syntactical._
import scala.util.parsing.input.CharArrayReader.EofCh

class PuppetParse extends RegexParsers
                  /* with StdTokenParsers */
                  with PackratParsers {

  type P[+T] = PackratParser[T]


  lazy val program: P[BlockExpr] =   stmts_and_decls 
                         /*    | (EofCh  ^^^ (BlockExpr (List[Branch] ()))) */


  lazy val stmts_and_decls: P[BlockExpr] = stmt_or_decl.* ^^ (BlockExpr (_))


  lazy val stmt_or_decl: P[AST] = (
    resource | virtualresource | collection | assignment | case_stmt | ifstmt_begin | 
    unless_stmt | import_stmt | fstmt | definition | hostclass | nodedef |
    resourceoverride | append | relationship
  )


  lazy val relationship: P[AST] = 
    relationship_side ~ (("<-" | "->" | "<-" | "->") ~ relationship_side).+ ^^ { 
      case rs ~ rss => rss.foldLeft (rs) { 
          case (x, "<-" ~ y) => RelationExpr (x, y, LeftSimpleDep)
          case (x, "->" ~ y) => RelationExpr (x, y, RightSimpleDep)
          case (x, "<~" ~ y) => RelationExpr (x, y, LeftSubscribeDep)
          case (x, "~>" ~ y) => RelationExpr (x, y, RightSubscribeDep)
        }
      }


  lazy val relationship_side: P[AST] = (
    resource | resourceref | collection | variable | quotedtext | selector | case_stmt |
    hasharrayaccesses
  )


  lazy val fstmt: P[Function] = (
    NAME ~ ("(" ~> expressions.? <~ ")") ^^ { 
      case n ~ Some (es) => Function (n, es, Ftstmt)
      case n ~ None => Function (n, List[AST] (), Fstmt)
    }
  | NAME ~ repsep(rvalue, ",") ^^ { 
      case n ~ rvs => Function (n, rvs, Ftstmt)
    }
  )


  lazy val expressions: P[List[AST]] = repsep (expr, ("," | "=>"))


  lazy val rvalue: P[AST] =
    quotedtext | name | asttype | boolean | selector | variable | array | hasharrayaccesses |
    resourceref | funcrvalue | undef
    

  lazy val resource: P[Branch] = (
    classname ~ ("{" ~> resourceinstances <~ ";".? <~ "}") ^^ {
      case cn ~ ris => Resource (cn, ris) 
    }
  | asttype ~ ("{" ~> params.? <~ ",".? <~ "}") ^^ {
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
  | "@@" ~> resource ^^ (VirtualResource (_, Vrtexported))
  )


  lazy val collection: P[Collection] = (
    asttype ~ collectrhand ~ ("{" ~> anyparams <~ ",".? <~ "}") ^^ {
      case t ~ cltrhnd ~ anyparams => Collection (t, cltrhnd, anyparams)
    }
  | asttype ~ collectrhand ^^ { 
      case t ~ cltrhnd => Collection (t, cltrhnd, List[ResourceParam] ())
    }
  )


  lazy val collectrhand: P[CollectionExprTagNode] = (
    "<|" ~> collstmts.? <~ "|>" ^^ (CollectionExprTagNode (_, Vrtvirtual))
  | "<<|" ~> collstmts.? <~ "|>>" ^^ (CollectionExprTagNode (_, Vrtexported))
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

  lazy val colllval: P[Leaf] = variable | name

  lazy val resourceinst: P[ResourceInstance] = 
    resourcename ~ (":" ~> params.? <~ ",".?) ^^ {
      case resnm ~ None => ResourceInstance (resnm, List ())
      case resnm ~ Some (params) => ResourceInstance (resnm, params)
    }

  lazy val resourceinstances: P[List[ResourceInstance]] = repsep (resourceinst, ";")

  lazy val undef: P[Leaf] = "undef" ^^^ Undef

  lazy val name: P[Name] = NAME ^^ (Name (_))


  lazy val asttype: P[Type] = CLASSREF ^^ (Type (_))


  lazy val resourcename: P[AST] =
    quotedtext | name | asttype | selector | variable | array | hasharrayaccesses


  lazy val assignment: P[Vardef] = (
    VARIABLE ~ ("=" ~> expr) ^^ { 
      case vrbl ~ e => Vardef (Name (vrbl), e, false)
    }
  | hasharrayaccess ~ ("=" ~> expr) ^^ { 
      case haa ~ e => Vardef (haa, e, false)
    }
  )

  lazy val append: P[Vardef] = 
    VARIABLE ~ ("+=" ~> expr) ^^ {
      case vrbl ~ e => Vardef (Name (vrbl), e, true)
    }

  lazy val params: P[List[ResourceParam]] = repsep (param, ",")

  lazy val param_name: P[Leaf] = NAME | keyword | BOOLEAN

  
  lazy val keyword: P[String] = "and" | "case" | "class" | "default" |
    "define" | "else" | "elsif" | "if" | "in" | "import" | "inherits" |
    "node" | "or" | "undef" | "unless"


  lazy val param: P[ResourceParam] = 
    param_name ~ ("=>" ~> expr) ^^ {
      case pn ~ e => ResourceParam (pn, e, false)
    }


  lazy val addparam: P[ResourceParam] = 
    NAME <~ "+>" ~> expr ^^ {
      case name ~ e => ResourceParam (name, e, true)
    }

  lazy val anyparams: P[List[ResourceParam]] = repsep ((param | addparam), ",")

  lazy val funcrvalue: P[Function] = 
    NAME <~ "(" ~> expressions.? <~ ")" ^^ {
      case name ~ Some (es) => Function (name, es,           Ftrval)
      case name ~ None      => Function (name, List[AST] (), Ftrval)
    }


  lazy val quotedstring: P[Leaf] = 
    STRING ^^ (ASTString (_))
  | (DQPRE ~ dqrval ^^ {
      case x ~ y => Concat (x, y)
    })


  lazy val dqrval: P[List[AST]] =
    expr ~ dqtail ^^ {
      case e ~ y => e :: y
    }


  lazy val dqtail: P[List[AST]] =
    DQPOST ^^ (List[ASTString] (ASTString (_)))
  | DQMID ~ dqrval ^^ {
      case x ~ y => x :: y
    }


  lazy val boolean: P[ASTBool] =
    BOOLEAN ^^ {
      case "true" => ASTBool (true)
      case "false" => ASTBool (false)
    }

  lazy val resourceref: P[ResourceRef] = (
    NAME <~ "[" ~> expressions <~ "]" ^^ {
      case name ~ e => ResourceRef (name, e)
    }
  | asttype <~ "[" ~> expressoins <~ "]" ^^ {
      case t ~ e => ResourceRef (t.value, e)
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
    "elsif" ~> ifstmt ^^ (BlockExpr (List (_)))
  | "else" ~> "{" ~> stmts_and_decls.? <~ "}" ^^ {
      case None => BlockExpr (List ())
      case Some (ss) => BlockExpr (ss)
    }
  )


  lazy val expr: P[AST] = (
    rvalue | hash
  | "-" ~> expr ^^ (UMinusExpr (_))
  | "!" ~> expr ^^ (NotExpr (_))
  | "(" ~> expr <~ ")"
  | (expr ~ ("=~" | "!~") ~ regex ^^ {
      case e ~ "=~" ~ r => MatchExpr (e, r, Match)
      case e ~ "!~" ~ r => MatchExpr (e, r, NoMatch)
    })
  | (expr ~ ("in" | "+" | "-" | "/" | "*" | "%" | "<<" | ">>" | "!=" | "==" | ">" | ">=" | "<" | "<=" | "and" | "or") ~ expr ^^ {
      case e1 ~ "in" ~ e2 => InExpr (e1, e2)
      case e1 ~ "+"  ~ e2 => ArithExpr (e1, e2, Plus)
      case e1 ~ "-"  ~ e2 => ArithExpr (e1, e2, Minus)
      case e1 ~ "/"  ~ e2 => ArithExpr (e1, e2, Div)
      case e1 ~ "*"  ~ e2 => ArithExpr (e1, e2, Mult)
      case e1 ~ "%"  ~ e2 => ArithExpr (e1, e2, Mod)
      case e1 ~ "<<" ~ e2 => ArithExpr (e1, e2, LShift)
      case e1 ~ ">>" ~ e2 => ArithExpr (e1, e2, RShift)
      case e1 ~ "!=" ~ e2 => CompareExpr (e1, e2, NotEqual)
      case e1 ~ "==" ~ e2 => CompareExpr (e1, e2, Equal)
      case e1 ~ ">"  ~ e2 => CompareExpr (e1, e2, GreaterThan) 
      case e1 ~ ">=" ~ e2 => CompareExpr (e1, e2, GreaterEq)
      case e1 ~ "<"  ~ e2 => CompareExpr (e1, e2, LessThan)
      case e1 ~ "<=" ~ e2 => CompareExpr (e1, e2, LessEq)
      case e1 ~ "and" ~ e2 => BoolBinExpr (e1, e2, And)
      case e1 ~ "or" ~ e2 =>  BoolBinExpr (e1, e2, Or)
    })
  )

  lazy val case_stmt: P[CaseExpr] = 
    "case" ~> expr ~ ("{" ~> caseopts <~ "}") ^^ {
      case e ~ csopts => CaseExpr (e, csopts)
    }

  lazy val caseopts: P[List[CaseOpt]] = (
    caseopt ^^ (List (_)) 
  | caseopts ~ caseopt ^^ {
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
  | "{" ~> sintvalues <~ ",".? <~ "}")

  lazy val sintvalues: P[List[ResourceParam]] = repsep (selectval, ("," | "=>"))

  lazy val selectval: P[ResourceParam] =
    selectlhand ~ ("=>" ~> rvalue) ^^ {
      case slcthnd ~ rval => ResourceParam (slcthnd, rval, false)
    }


  lazy val selectlhand: P[AST] = (
    name | asttype | quotedtext | variable | funcrvalue | boolean | undef |
    hasharrayaccess | ("default" ^^^ Default) | regex
  )
    
  
  lazy val string: P[String] = STRING

  lazy val strings: P[List[String]] = repsep (string, ",") 

  lazy val import_stmt: P[Import] = 
    "import" ~> strings ^^ (Import (_))

  lazy val definition: P[Definition] = 
    "define" ~> classname ~ argumentlist ~ ("{" ~> stmts_and_decls.? <~ "}") ^^ {
      case cnm ~ args ~ None      => Definition (cnm, args, BlockExpr (List ()))
      case cnm ~ args ~ Some (ss) => Definition (cnm, args, ss)
    }

  lazy val hostclass: P[Hostclass] = 
    "class" ~> classname ~ argumentlist ~ classparent.? ~ ("{" ~> stmts_and_decls.? <~ "}") ^^ {
      case cnm ~ args ~ clp ~ None => Hostclass (cnm, args, clp, BlockExpr (List ()))
      case cnm ~ args ~ clp ~ Some (ss) => Hostclass (cnm, args, clp, ss)
    }

  lazy val nodedef: P[Node] = (
    "node" ~> hostnames ~ nodeparent.? ~ ("{" ~> stmts_and_decls.? <~ "}") ^^ {
      case hosts ~ ndp ~ None => Node (hosts, ndp, BlockExpr (List ()))
      case hosts ~ ndp ~ Some (ss) => Node (hosts, ndp, ss)
    }
  )

  lazy val classname: P[String] = NAME | "class"

  lazy val hostnames: P[List[Hostname]] = repsep (nodename, ",") 

  lazy val nodename: P[Hostname] = hostname ^^ (Hostname (_))

  lazy val hostname: P[String] = NAME | STRING | "default" | regex

  lazy val argumentlist: P[List[(String, Option[Branch])]] = (
    "(" ~> arguments.? <~ ")" ^^ {
      case None => List ()
      case Some (ss) => ss
    }
  | "(" ~> arguments <~ ",".? <~ ")"
  )

  lazy val arguments: P[List[(String, Option[Branch])]] = repsep (argument, ",")

  lazy val argument: P[(String, Option[Branch])] = (
    VARIABLE ~ ("=" ~> expr) ^^ { case v ~ e => (v, Some (e)) }
  | VARIABLE ^^ ((_, None))
  )

  lazy val nodeparent: P[String] = "inherits" ~> hostname

  lazy val classparent: P[String] = "inherits" ~> (classname | "default")

  lazy val variable: P[Variable] = VARIABLE ^^ (Variable (_))

  lazy val array: P[ASTArray] = (
    "[" ~> expressions.? <~ "]" ^^ {
      case None => ASTArray (List ())
      case Some (es) => ASTArray (es)
    }
  | "[" ~> expressions <~ "," <~ "]" ^^ (ASTArray (_))
  )

  lazy val regex: P[ASTRegex] = REGEX ^^ (ASTRegex (_))

  lazy val hash: P[ASTHash] = (
    "{" ~> hashpairs.? <~ "}" ^^ {
      case None => ASTHash (List ())
      case Some (kvs) => ASTHash (kvs)
    }
  | "{" ~> hashpairs <~ ",".? <~ "}" ^^ (ASTHash (_))
  )

  lazy val hashpairs: P[List[(String, AST)]] = repsep (hashpair, ",")

  lazy val hashpair: P[(String, AST)] = key ~ ("=>" ~> expr) ^^ {
    case k ~ e => (k, e)
  }

  lazy val key: P[String] = NAME | quotedtext

  lazy val hasharrayaccess: P[HashOrArrayAccess] =
    variable ~ ("[" ~> expr <~ "]") ^^ {
      case v ~ e => HashOrArrayAccess (v, e)
    }

  lazy val hasharrayaccesses: P[HashOrArrayAccess] = (
    hasharrayaccess 
  | hasharrayaccesses ~ ("[" ~> expr <~ "]") ^^ {
      case haa ~ e => HashOrArrayAccess (haa, e)
    }
  )
    
  // TODO : NAME
  // TODO : STRING
  // TODO : REGEX
  // TODO : BOOLEAN
  // TODO : DQPRE, DQMID, DQPOST
  // TODO : quotedtext
  // TODO : Comments
}
