object PrettyPrintAST {

  private def ArithOpStr (op: ArithOp): String = op match {
   case Plus   => "+"
   case Minus  => "-"
   case Div    => "/"
   case Mult   => "*"
   case Mod    => "%"
   case LShift => "<<"
   case RShift => ">>"
  }

  private def BoolBinOpStr (op: BoolBinOp): String = op match {
     case And => "and"
     case Or  => "or"
  }

  private def CompareOpStr (op: CompareOp): String = op match {
    case NotEqual    => "!="
    case Equal       => "=="
    case GreaterThan => ">"
    case GreaterEq   => ">="
    case LessThan    => "<"
    case LessEq      => "<="
  }

  private def MatchOpStr (op: MatchOp): String = op match { 
    case Match => "=~"
    case NoMatch => "!~"
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
    case ArithExpr    (lhs, rhs, op) => printAST (lhs) + " " + ArithOpStr (op)   + " " + printAST (rhs)
    case BoolBinExpr  (lhs, rhs, op) => printAST (lhs) + " " + BoolBinOpStr (op) + " " + printAST (rhs)
    case CompareExpr  (lhs, rhs, op) => printAST (lhs) + " " + CompareOpStr (op) + " " + printAST (rhs)
    case InExpr       (lhs, rhs)     => printAST (lhs) + " in " + printAST (rhs)
    case RelationExpr (lhs, rhs, op) => printAST (lhs) + " " + RelationOpStr (op) + " " + printAST (rhs)
    case MatchExpr    (lhs, rhs, op) => printAST (lhs) + " " + MatchOpStr (op) + " " + printAST (rhs)
    case NotExpr (ne) => "!" + printAST (ne)
    case UMinusExpr (ume) => "-" + printAST (ume)
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
