object PrettyPrintAST {

  private def BinOpStr (op: BinOp): String = op match {

    case Or          => "or"

    case And         => "and"

    case GreaterThan => ">"
    case GreaterEq   => ">="
    case LessThan    => "<"
    case LessEq      => "<="

    case NotEqual    => "!="
    case Equal       => "=="

    case LShift      => "<<"
    case RShift      => ">>"

    case Plus        => "+"
    case Minus       => "-"

    case Div         => "/"
    case Mult        => "*"
    case Mod         => "%"

    case Match       => "=~"
    case NoMatch     => "!~"
    case In          => "in"
  }

  private def RelationOpStr (op: RelationOp): String = op match {
    case LeftSimpleDep     => "<-"
    case RightSimpleDep    => "->"
    case LeftSubscribeDep  => "<~"
    case RightSubscribeDep => "~>"
  }

  private def CollectionOpStr (op: CollectionOp): String = op match {
    case CollOr    => "or"
    case CollAnd   => "and"
    case CollIsEq  => "=="
    case CollNotEq => "!="
  }

  private def VirtualResTypeStr (op: VirtualResType): String = op match {
    case Vrtvirtual  => "@"
    case Vrtexported => "@@"
  }




  private sealed abstract class ExprContext;

  private case object OR_L extends ExprContext;
  private case object OR_R extends ExprContext;

  private case object AND_L extends ExprContext;
  private case object AND_R extends ExprContext;

  private case object RELATIONAL_L extends ExprContext;
  private case object RELATIONAL_R extends ExprContext;

  private case object NOTEQUAL_EQUAL_L extends ExprContext;
  private case object NOTEQUAL_EQUAL_R extends ExprContext;
  
  private case object LSHIFT_RSHIFT_L extends ExprContext;
  private case object LSHIFT_RSHIFT_R extends ExprContext;

  private case object PLUS_MINUS_L extends ExprContext;
  private case object PLUS_MINUS_R extends ExprContext;

  private case object DIV_MULT_MOD_L extends ExprContext;
  private case object DIV_MULT_MOD_R extends ExprContext;

  private case object IN_MATCH_NOMATCH_L   extends ExprContext;
  private case object IN_MATCH_NOMATCH_R   extends ExprContext;

  private case object NOT    extends ExprContext;
  private case object UMINUS extends ExprContext;

  private case object TOPLEVEL extends ExprContext;


  private def parensRequired (op: BinOp, context: ExprContext) : Boolean = op match {

    case In | NoMatch | Match => context match {
      case NOT | UMINUS | IN_MATCH_NOMATCH_R => true
      case _ => false
    }

    case Mod | Mult | Div => context match {
      case NOT | UMINUS | IN_MATCH_NOMATCH_R | 
           IN_MATCH_NOMATCH_L | DIV_MULT_MOD_R => true
      case _ => false
    }

    case Plus | Minus => context match {
      case NOT | UMINUS | IN_MATCH_NOMATCH_R |
           IN_MATCH_NOMATCH_L | DIV_MULT_MOD_R |
           DIV_MULT_MOD_L | PLUS_MINUS_R => true
      case _ => false
    }

    case LShift | RShift => context match {
      case NOT | UMINUS | IN_MATCH_NOMATCH_R |
           IN_MATCH_NOMATCH_L | DIV_MULT_MOD_R |
           DIV_MULT_MOD_L | PLUS_MINUS_R | PLUS_MINUS_L |
           LSHIFT_RSHIFT_R => true
      case _ => false
    }

    case NotEqual | Equal => context match {
      case NOT | UMINUS | IN_MATCH_NOMATCH_R |
           IN_MATCH_NOMATCH_L | DIV_MULT_MOD_R |
           DIV_MULT_MOD_L | PLUS_MINUS_R |
           PLUS_MINUS_L | LSHIFT_RSHIFT_R |
           LSHIFT_RSHIFT_L | NOTEQUAL_EQUAL_R => true
      case _ => false
    }

    case GreaterThan | GreaterEq | LessThan | LessEq => context match {
      case NOT | UMINUS | IN_MATCH_NOMATCH_R |
           IN_MATCH_NOMATCH_L | DIV_MULT_MOD_R |
           DIV_MULT_MOD_L | PLUS_MINUS_R |
           PLUS_MINUS_L | LSHIFT_RSHIFT_R |
           LSHIFT_RSHIFT_L | NOTEQUAL_EQUAL_R |
           RELATIONAL_R => true
      case _ => false
    }

    case And => context match {
      case NOT | UMINUS | IN_MATCH_NOMATCH_R |
           IN_MATCH_NOMATCH_L | DIV_MULT_MOD_R |
           DIV_MULT_MOD_L | PLUS_MINUS_R |
           PLUS_MINUS_L | LSHIFT_RSHIFT_R |
           LSHIFT_RSHIFT_L | NOTEQUAL_EQUAL_R |
           RELATIONAL_R | RELATIONAL_L | AND_R => true
      case _ => false
    }

    case Or => context match {
      case NOT | UMINUS | IN_MATCH_NOMATCH_R |
           IN_MATCH_NOMATCH_L | DIV_MULT_MOD_R |
           DIV_MULT_MOD_L | PLUS_MINUS_R |
           PLUS_MINUS_L | LSHIFT_RSHIFT_R |
           LSHIFT_RSHIFT_L | NOTEQUAL_EQUAL_R |
           RELATIONAL_R | RELATIONAL_L | AND_R |
           AND_L | OR_R => true
      case _ => false
    }
  }


  private def printBinExprWithCtx (lhs: AST, rhs: AST, op: BinOp, lctx: ExprContext, rctx: ExprContext) = {
    printExpr (lhs, lctx) + " " + BinOpStr (op) + " " + printExpr (rhs, rctx)
  }


  private def printExpr (a: AST, context: ExprContext) : String = a match {

    case BinExpr (lhs, rhs, op) =>
      def printer (x: String) = if (parensRequired (op, context)) "(" + x + ")" else x

      op match {

      case In | NoMatch | Match => printer (printBinExprWithCtx (lhs, rhs, op, IN_MATCH_NOMATCH_L, IN_MATCH_NOMATCH_R))
      case Mod | Mult | Div     => printer (printBinExprWithCtx (lhs, rhs, op, DIV_MULT_MOD_L, DIV_MULT_MOD_R))
      case Plus | Minus         => printer (printBinExprWithCtx (lhs, rhs, op, PLUS_MINUS_L, PLUS_MINUS_R))
      case LShift | RShift      => printer (printBinExprWithCtx (lhs, rhs, op, LSHIFT_RSHIFT_L, LSHIFT_RSHIFT_R))
      case NotEqual | Equal     => printer (printBinExprWithCtx (lhs, rhs, op, NOTEQUAL_EQUAL_L, NOTEQUAL_EQUAL_R))

      case GreaterThan | GreaterEq | 
           LessThan | LessEq    => printer (printBinExprWithCtx (lhs, rhs, op, RELATIONAL_L, RELATIONAL_R))

      case And => printer (printBinExprWithCtx (lhs, rhs, op, AND_L, AND_R))

      case Or => printer (printBinExprWithCtx (lhs, rhs, op, OR_L, OR_R))
    }

    // Op implicitly is "NOT" not in context of case
    case NotExpr (ne) => "!" + "(" + printExpr (ne, NOT) +")"

    // Op implicity is "UMINUS"
    case UMinusExpr (ume) => "-" + "(" + printExpr (ume, UMINUS) + ")"

    case _ => printAST (a)
  }
    

  private def printList[T] (lst: List[T], f: T => String, sep: String): String = {
    (lst.map (f)) mkString sep 
  }

  def printAST (ast: AST): String = ast match {

    case ASTBool (true)           => "true"
    case ASTBool (false)          => "false"
    case ASTString (s)            => if (s.exists ({_ == '\''})) "\"" + s + "\""
                                     else "\'" + s + "\'"
    case Concat (lhs, rhs)        => printAST (lhs) + " " + printAST (rhs)
    case Default                  => "default"
    case Type (v)                 => v
    case Name (v)                 => v
    case Undef                    => "undef"
    case Hostname (v)             => v
    case Variable (v)             => v
    case HashOrArrayAccess (v, k) => printAST (v) + "[" + printAST (k) + "]"
    case ASTRegex (v)             => v
    case ASTHash (kvs)            => "{" + printList[(AST, AST)] (kvs, {case (k, v) => (printAST (k)) + " => " + (printAST (v))}, ", ") + "}"

    case BlockExpr (es) => printList (es, printAST, "\n") 
    
    // TODO : Parentheses and precedence
    case BinExpr (_, _, _) => printExpr (ast, TOPLEVEL)
    case RelationExpr (lhs, rhs, op) => printAST (lhs) + " " + RelationOpStr (op) + " " + printAST (rhs)
    case NotExpr (_)    => printExpr (ast, TOPLEVEL)
    case UMinusExpr (_) => printExpr (ast, TOPLEVEL)
    case Vardef (nm, v, is_append) => printAST (nm) + (if (is_append) " += " else " = ") + printAST (v)
    case ASTArray (arr) => "[" + printList (arr, printAST, ",") + "]" 
    case ResourceParam (p, v, is_add) => printAST (p) + (if(is_add) " +> " else " => ") + printAST (v)
    case ResourceInstance (t, prms) => printAST (t) + ": " + printList (prms, printAST, ",\n")
    case Resource (typ, insts) => typ + " " + "{" + printList (insts, printAST, ";\n") + "}"
    case ResourceDefaults (typ, prms) => printAST (typ) + " " + "{" + "\n" + printList (prms, printAST, ", ") + "\n}"
    case ResourceRef (typ, es) => printAST (typ) + " " + "[" + printList (es, printAST, ", ") + "]"
    case ResourceOverride (obj, prms) => printAST (obj) + " " + "{" + "\n" + printList (prms, printAST, ",\n") + "\n}"

    case VirtualResource (res, tvirt) => VirtualResTypeStr (tvirt) + printAST (res)
    case IfExpr (test, true_es, false_es) => "if" + " " + printAST (test) + " { " + printAST (true_es) + " } else { " + printAST (false_es) + "}\n"

    case CaseOpt (v, stmts) => printList (v, printAST, ", ") + " : " + "{" + "\n" + printAST (stmts) + "}" + "\n"

    case CaseExpr (test, caseopts) => "case" + " " + printAST (test) + " " + "{" + "\n" + printList (caseopts, printAST, " ") + "\n" + "}" + "\n"

    case Selector (prm, vs) => printAST (prm) + " " + "?" + " " + "{" + "\n" + printList (vs, printAST, ",\n") + "}"
    case CollectionExpr (lhs, rhs, op) => printAST (lhs) + " " + CollectionOpStr (op) + " " + printAST (rhs)

    case CollectionExprTagNode (None, prop) => if (prop == Vrtvirtual) "<| |>" else "<<| |>>"
    case CollectionExprTagNode (Some (coll), prop) => 
      if (prop == Vrtvirtual) ("<|" + " " + printAST (coll) + " " + "|>")
      else ("<<|" + " " + printAST (coll) + " " + "|>>")

    case Collection (typ, collectrhand, Nil) => printAST (typ) + " " + printAST (collectrhand)
    case Collection (typ, collectrhand, prms) => printAST (typ) + " " + printAST (collectrhand) + " " + "{" + "\n" + printList (prms, printAST, ",") + "}" + "\n"

    case Hostclass (clnm, Nil, None, stmts) => "class" + " " + clnm + " " + "{" + "\n" + printAST (stmts) + "}" + "\n"
    case Hostclass (clnm, args, None, stmts) => "class" + " " + clnm + " " + "(" + printList[(String, Option[AST])] (args, { case (v, None) => v
                                                                                                      case (v, Some (e)) => v + " = " + printAST(e)}, ",") + ")" + " " + "{" + "\n" + printAST (stmts) + "}" + "\n"
    case Hostclass (clnm, Nil, Some (parent), stmts) => "class" + " " + clnm + " " + "inherits" + " " + parent + "{" + "\n" + printAST (stmts) + "}" + "\n"
    case Hostclass (clnm, args, Some (parent), stmts) => "class" + " " + clnm + " " + "inherits" + " " + parent + " " + "(" + printList[(String, Option[AST])] (args, { case (v, None) => v
                                                                                                      case (v, Some (e)) => v + " = " + printAST(e)}, ",")  + ")" + " " + "{" + "\n" + printAST (stmts) + "}" + "\n"

    case Function (nm, args, _) => nm + " " + "(" + " " + printList (args, printAST, ",") + " " + ")"

    case Import (imps) => "import" + " " + printList (imps, (x: String) => x, ",") + "\n"

    case Node (hostnames, None, es) => "node" + " " + printList (hostnames, printAST, ",") + " " + "{" + "\n" + printAST (es) + "}" + "\n"

    case Node (hostnames, Some (parent), es) => "node" + " " + printList (hostnames, printAST, ",") + " " + "inherits" + " " + parent + " " + "{" + "\n" + printAST (es) + "}" + "\n"

    case Definition (classname, Nil, es) => "define" + " " + classname + " " + "{" + "\n" + printAST (es) + "}" + "\n"
    case Definition (classname, args, es) => "define" + " " + classname + " " + "(" + printList[(String, Option[AST])](args, { case (v, None) => v
                                                                                                         case (v, Some (e)) => v + " = " + printAST (e)}, ",") + ")" + " " + "{" + "\n" + printAST (es) + "}" + "\n"
  }
}
