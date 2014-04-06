/* Parser using parser combinator in Scala */

import scala.util.parsing.combinator._
import scala.util.parsing.combinator.syntactical._
import scala.util.parsing.input.CharArrayReader.EofCh

class PuppetParse extends RegexParsers
                  /* with StdTokenParsers */
                  with PackratParsers {

  type P[+T] = PackratParser[T]


  lazy val program: P[AST] =   stmts_and_decls 
                             | (EofCh  ^^^ (ASTNothing))


  lazy val stmts_and_decls: P[BlockExpr] = stmt_or_decl.* ^^ (BlockExpr (_))


  lazy val stmt_or_decl: P[Branch] =
    resource | virtualresource | collection | assignment | casestmts | ifstmt_begin | 
    unless_stmt | import_stmt | fstmt | definition | hostclass | nodedef |
    resourceoverride | append | relationship


  lazy val relationship: P[RelationExpr] = 
    relationship_side ~ (("<-" | "->" | "<-" | "->") ~ relationship_side).+ ^^ { 
      case rs::rss => rss.foldLeft(rs) { 
          case (x, "<-" ~ y) => RelationExpr (x, y, LeftSimpleDep)
          case (x, "->" ~ y) => RelationExpr (x, y, RightSimpleDep)
          case (x, "<~" ~ y) => RelationExpr (x, y, LeftSubscribeDep)
          case (x, "~>" ~ y) => RelationExpr (x, y, RightSubscribeDep)
        }
      }


  lazy val relationship_side: P[AST] = 
    resource | resourceref | collection | variable | quotedtext | selector | casestatement |
    hasharrayaccesses


  lazy val fstmt: P[Function] = 
    NAME ~ "(" ~> repsep(expr, ",") <~ ")" ^^ { case n ~ es => Function (n, es, Ftstmt) }
  | NAME ~ repsep(rvalue, ",") ^^ { case n ~ rvs => Function (n, rvs, Ftstmt) }


  lazy val rvalue: P[AST] =
    quotedtext | name | asttype | boolean | selector | variable | array | hasharrayaccesses |
    resourceref | funcrvalue | undef
    

  lazy val resource: P[Branch] = 
    classname ~ "{" ~> repsepi (resourceinstance, ";") <~ "}" ^^ {
      case cn~ris => Resource (cn, ris) 
    }
  | asttype ~ "{" ~> repsep(param, ",") <~ "}" ^^ {
      case t~params => ResourceDefaults (t, params)
    }


  lazy val resourceoverride: P[ResourceOverride] =
    resourceref ~ "{" ~> repsep(anyparam, ",") <~ "}" ^^ {
      case rref~anyparams => ResourceOverride (rref, anyparams)
    }


  lazy val virtualresource: P[VirtualResource] =
    "@" ~> resource ^^ (VirtualResource (_, Vrtvirtual))
  | "@@" ~> resource ^^ (VirtualResource (_, Vrtexported))


  lazy val collection: P[Collection] =
    asttype ~ collectrhand ~ "{" ~> repsep (anyparam, ",") <~ "}" ^^ {
      case t~cltrhnd~anyparams => Collection (t, cltrhnd, anyparams)
    }
  | asttype ~ collectrhand ^^ { case t~cltrhnd => Collection (t, cltrhnd, []) }


  lazy val collectrhand: P[CollectionExprTagNode] =
    "<|" ~> collstmts <~ "|>" ^^ (CollectionExprTagNode (_, Vrtvirtual))
  | "<<|" ~> collstmts <~ "|>>" ^^ (CollectionExprTagNode (_, Vrtexported))

  lazy val collstmts: P[Option[CollectionExpr]] =
    "" ^^ (None)
  | collstmt ^^ (Some _)
  | collstmts ~ ("and" | "or") ~ collstmt ^^ {
      case x ~ "and" ~ y => Some (CollectionExpr (x, y, CollAnd)
      case x ~ "or"  ~ y => Some (CollectionExpr (x, y, CollOr)
    }


  lazy val collstmt: P[CollectionExpr] =
    collexpr | "(" ~> collstmts <~ ")"

  lazy val collexpr: P[CollectionExpr] =
    colllval ~ ("==" | "!=") ~ expr ^^ {
      case x ~ "==" ~ y => Some (CollectionExpr (x, y, CollIsEq)
      case x ~ "!=" ~ y => Some (CollectionExpr (x, y, CollNotEq)
    }


  lazy val colllval: P[Leaf] = variable | name


  lazy val resourceinst: P[ResourceInstance] = 
    resourcename <~ ":" ~> repsep (param, ",") ^^ {
      case resnm ~ params => ResourceInstance (resnm, params)
    }


  lazy val resourceinstances: P[List[ResourceInstance]] =
    repsep (resourceinst, ";")


  lazy val undef: P[Leaf] = "undef" ^^^ Leaf


  lazy val name: P[Name] = NAME ^^ (Name (_))


  lazy val asttype: P[Type] = CLASSREF ^^ (Type (_))


  lazy val resourcename: P[AST] =
    quotedtext | name | asttype | selector | variable | array | hasharrayaccesses


  lazy val assignment: P[Vardef] =
    VARIABLE ~ ("=" | "+=") ~ expr ^^ { 
      case vrbl ~ "="  ~ e => Vardef (Name (vrbl), e, SimplAssign)
      case vrbl ~ "+=" ~ e => Vardef (Name (vrbl), e, AppendAsign)
    }
  | hasharrayaccess <~ "=" ~> expr ^^ { 
      case haa ~ e => Vardef (haa, e, SimplAssign)
    }


  lazy val params: P[ASTArray] =
    "" ^^ ASTArray (List[Branch] ())
  | repsep (param, ",")


  lazy val param_name: P[LEAF] = NAME | keyword | BOOLEAN

  
  lazy val keyword: P[LEAF] = /* TODO */


  lazy val param: P








    


  // TODO : Name has to be regex
}
