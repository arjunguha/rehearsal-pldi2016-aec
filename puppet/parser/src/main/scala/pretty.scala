package puppet;

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


  private sealed abstract class DirContext;
  private case object LEFT  extends DirContext;
  private case object RIGHT extends DirContext;


  private sealed abstract class ExprContext;
  private case class OR               (dir: DirContext) extends ExprContext;
  private case class AND              (dir: DirContext) extends ExprContext;
  private case class RELATIONAL       (dir: DirContext) extends ExprContext;
  private case class NOTEQUAL_EQUAL   (dir: DirContext) extends ExprContext;
  private case class LSHIFT_RSHIFT    (dir: DirContext) extends ExprContext;
  private case class PLUS_MINUS       (dir: DirContext) extends ExprContext;
  private case class DIV_MULT_MOD     (dir: DirContext) extends ExprContext;
  private case class IN_MATCH_NOMATCH (dir: DirContext) extends ExprContext;
  private case object NOT      extends ExprContext;
  private case object UMINUS   extends ExprContext;
  private case object TOPLEVEL extends ExprContext;


  private def parensRequired (op: BinOp, context: ExprContext) : Boolean = op match {

    case In | NoMatch | Match => context match {
      case NOT | UMINUS | IN_MATCH_NOMATCH (RIGHT) => true
      case _ => false
    }

    case Mod | Mult | Div => context match {
      case NOT | UMINUS | IN_MATCH_NOMATCH (_) |
           DIV_MULT_MOD (RIGHT) => true
      case _ => false
    }

    case Plus | Minus => context match {
      case NOT | UMINUS | IN_MATCH_NOMATCH (_) |
           DIV_MULT_MOD (_) | PLUS_MINUS (RIGHT) => true
      case _ => false
    }

    case LShift | RShift => context match {
      case NOT | UMINUS | IN_MATCH_NOMATCH (_) | 
           DIV_MULT_MOD (_) | PLUS_MINUS (_) | 
           LSHIFT_RSHIFT (RIGHT) => true
      case _ => false
    }

    case NotEqual | Equal => context match {
      case NOT | UMINUS | IN_MATCH_NOMATCH (_) | 
           DIV_MULT_MOD (_) | PLUS_MINUS (_)   |
           LSHIFT_RSHIFT (_) | NOTEQUAL_EQUAL (RIGHT) => true
      case _ => false
    }

    case GreaterThan | GreaterEq | LessThan | LessEq => context match {
      case NOT | UMINUS | IN_MATCH_NOMATCH (_) | 
           DIV_MULT_MOD (_) | PLUS_MINUS (_)   |
           LSHIFT_RSHIFT (_) | NOTEQUAL_EQUAL (_) |
           RELATIONAL (RIGHT) => true
      case _ => false
    }

    case And => context match {
      case NOT | UMINUS | IN_MATCH_NOMATCH (_) | 
           DIV_MULT_MOD (_) | PLUS_MINUS (_) |
           LSHIFT_RSHIFT (_) | NOTEQUAL_EQUAL (_) |
           RELATIONAL (_) | AND (RIGHT) => true
      case _ => false
    }

    case Or => context match {
      case NOT | UMINUS | IN_MATCH_NOMATCH (_) |
           DIV_MULT_MOD (_) | PLUS_MINUS (_) |
           LSHIFT_RSHIFT (_) | NOTEQUAL_EQUAL (_) |
           RELATIONAL (_) | AND (_) | OR (RIGHT) => true
      case _ => false
    }
  }


  private def printBinExprWithCtx (lhs: AST, rhs: AST, op: BinOp, lctx: ExprContext, rctx: ExprContext) = {
    printExpr (lhs, lctx) + " " + BinOpStr (op) + " " + printExpr (rhs, rctx)
  }


  // TODO : Could be refactored
  private def printExpr (a: AST, context: ExprContext) : String = a match {

    case BinExpr (lhs, rhs, op) =>
      def printer (x: String) = if (parensRequired (op, context)) "(%s)".format (x) else x

      op match {

      case In | NoMatch | Match => printer (printBinExprWithCtx (lhs, rhs, op, IN_MATCH_NOMATCH (LEFT), IN_MATCH_NOMATCH (RIGHT)))
      case Mod | Mult | Div     => printer (printBinExprWithCtx (lhs, rhs, op, DIV_MULT_MOD (LEFT), DIV_MULT_MOD (RIGHT)))
      case Plus | Minus         => printer (printBinExprWithCtx (lhs, rhs, op, PLUS_MINUS (LEFT), PLUS_MINUS (RIGHT)))
      case LShift | RShift      => printer (printBinExprWithCtx (lhs, rhs, op, LSHIFT_RSHIFT (LEFT), LSHIFT_RSHIFT (RIGHT)))
      case NotEqual | Equal     => printer (printBinExprWithCtx (lhs, rhs, op, NOTEQUAL_EQUAL (LEFT), NOTEQUAL_EQUAL (RIGHT)))

      case GreaterThan | GreaterEq | 
           LessThan | LessEq    => printer (printBinExprWithCtx (lhs, rhs, op, RELATIONAL (LEFT), RELATIONAL (RIGHT)))

      case And => printer (printBinExprWithCtx (lhs, rhs, op, AND (LEFT), AND (RIGHT)))

      case Or => printer (printBinExprWithCtx (lhs, rhs, op, OR (LEFT), OR (RIGHT)))
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

    case ASTBool (true)            => "true"
    case ASTBool (false)           => "false"
    case ASTString (s)             => if (s.exists ({_ == '\''})) "\"" + s + "\""
                                      else "\'" + s + "\'"
    case Default                   => "default"
    case Type (v)                  => v
    case Name (v)                  => v
    case Undef                     => "undef"
    case Variable (v)              => v
    case HashOrArrayAccess (v, ks) => "%s[%s]".format (printAST (v), printList (ks, printAST, "][")) // Hackish
    case ASTRegex (v)              => v
    case ASTHash (kvs)             => "{%s}".format (printList[(AST, AST)] (kvs, {case (k, v) => "%s => %s".format (printAST (k), printAST (v))}, ", "))

    case BlockStmtDecls (es) => printList (es, printAST, "\n") 
    
    case BinExpr (_, _, _) => printExpr (ast, TOPLEVEL)
    case RelationExpr (lhs, rhs, op) => "%s %s %s".format (printAST (lhs), RelationOpStr (op), printAST (rhs))
    case NotExpr (_)    => printExpr (ast, TOPLEVEL)
    case UMinusExpr (_) => printExpr (ast, TOPLEVEL)
    case Vardef (nm, v, true)  => "%s += %s".format (printAST (nm), printAST (v))
    case Vardef (nm, v, false) => "%s = %s".format (printAST (nm), printAST (v))
    case ASTArray (arr) => "[%s]".format (printList (arr, printAST, ","))
    case Attribute (name, value, true)  => "%s +> %s".format (printAST (name), printAST (value))
    case Attribute (name, value, false) => "%s => %s".format (printAST (name), printAST (value))
    case ResourceInstance (t, prms) => "%s: %s".format (printAST (t), printList (prms, printAST, ",\n"))
    case Resource (typ, insts) => "%s { %s }".format (typ, printList (insts, printAST, ";\n"))
    case ResourceDefaults (typ, prms) => "%s {\n%s\n}".format (printAST (typ), printList (prms, printAST, ", "))
    case ResourceRef (typ, es) => "%s [%s]".format (printAST (typ), printList (es, printAST, ", "))
    case ResourceOverride (obj, prms) => "%s {\n%s\n}".format (printAST (obj), printList (prms, printAST, ",\n"))

    case VirtualResource (res, tvirt) => "%s%s".format (VirtualResTypeStr (tvirt), printAST (res))
    case IfExpr (test, true_es, false_es) => "if %s { %s } else { %s }".format (printAST (test), printList (true_es, printAST, "\n"), printList (false_es, printAST, "\n"))
    case CaseOpt (v, stmts) => "%s : {\n %s \n}".format (printList (v, printAST, ", "), printList (stmts, printAST, "\n"))

    case CaseExpr (test, caseopts) => "case %s {\n%s\n}".format (printAST (test), printList (caseopts, printAST, " "))

    case Selector (prm, vs) => "%s ? {\n%s\n}".format (printAST (prm), printList (vs, printAST, ",\n"))
    case CollectionExpr (lhs, rhs, op) => "%s %s %s".format (printAST (lhs), CollectionOpStr (op), printAST (rhs))

    case Collection (typ, filterexpr, restype, attribs) => {
      restype match {
        case Vrtvirtual => "%s <| %s |> %s".format (printAST (typ), 
                                                    (filterexpr match { case None => ""; case Some (expr) => printAST (expr) }),
                                                    (if (attribs.length > 0) "{\n%s\n}".format (printList (attribs, printAST, "\n")) else ""))
        case Vrtexported => "%s <<| %s |>> %s".format (printAST (typ), 
                                                    (filterexpr match { case None => ""; case Some (expr) => printAST (expr) }),
                                                    (if (attribs.length > 0) "{\n%s\n}".format (printList (attribs, printAST, "\n")) else ""))
      }
    }

    case Hostclass (clnm, Nil, None, stmts) => "class %s {\n%s\n}".format (clnm, printAST (stmts))
    case Hostclass (clnm, args, None, stmts) => "class %s (%s) {\n%s\n}".format (clnm, printList[(Variable, Option[Expr])] (args, { case (v, None) => printAST (v)
                                                                                                                                   case (v, Some (e)) => "%s = %s".format (printAST (v), printAST(e))
                                                                                                                               }, ","), printAST (stmts))
    case Hostclass (clnm, Nil, Some (parent), stmts) => "class %s inherits %s {\n%s\n}".format (clnm, parent, printAST (stmts))
    case Hostclass (clnm, args, Some (parent), stmts) => 
      "class %s (%s) inherits %s {\n%s\n}".format (clnm, 
                                                   printList[(Variable, Option[Expr])] (args, { 
                                                     case (v, None) => printAST (v)
                                                     case (v, Some (e)) =>"%s = %s".format (printAST (v), printAST(e))
                                                   }, ","),
                                                   parent, printAST (stmts))

    case Function (nm, args, _) => "%s (%s)".format (printAST (nm), printList (args, printAST, ","))

    case Import (imps) => "import %s\n".format (printList (imps, (x: String) => "\"%s\"".format (x), ","))

    case Node (hostnames, None, es) => "node %s {\n%s\n}".format (printList (hostnames, printAST, ","), printList (es, printAST, "\n"))

    case Node (hostnames, Some (parent), es) => "node %s inherits %s {\n%s\n}".format (printList (hostnames, printAST, ","), parent, printList (es, printAST, "\n"))

    case Definition (classname, Nil, es) => "define %s {\n%s\n}".format (classname, printList (es, printAST, "\n"))
    case Definition (classname, args, es) => "define %s (%s) {\n%s\n}".format (classname, printList[(Variable, Option[Expr])](args, { case (v, None) => printAST (v)
                                                                                                                                     case (v, Some (e)) => "%s = %s".format (printAST (v), printAST (e))
                                                                                                                                 }, ","), printList (es, printAST, "\n"))
  }
}
