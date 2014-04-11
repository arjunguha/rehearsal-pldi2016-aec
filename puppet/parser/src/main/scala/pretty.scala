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

  def printAST (ast: AST): String = ast match {

    case ASTBool (true)           => "true"
    case ASTBool (false)          => "false"
    case ASTString (s)            => s
    case Concat (lhs, rhs)        => printAST (lhs) + " " + printAST (rhs)
    case Default                  => "default"
    case Type (v)                 => v
    case Name (v)                 => v
    case Undef                    => "undef"
    case Hostname (v)             => v
    case Variable (v)             => v
    case HashOrArrayAccess (v, k) => printAST (v) + "[" + printAST (k) + "]"
    case ASTRegex (v)             => v
    case ASTHash (kvs)            => "{" + 
                                        kvs.foldLeft ("") { 
                                          case (acc, (leaf, ast)) => 
                                            acc + " " + printAST (leaf) + " => " + printAST (ast) + ", "
                                            } +
                                      "}"

    case BlockExpr (es) => es.foldLeft ("") { case (acc, ast) => printAST (ast) + "\n" }
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
    case ASTArray (arr) => "[" + 
                              arr.foldLeft ("") { case (acc, x) => acc + printAST (x) + ", "} +
                           "]"
    case ResourceParam (p, v, is_add) => printAST (p) + (if(is_add) " +> " else " => ") + printAST (v)
    case ResourceInstance (t, prms) => printAST (t) + ": " + 
                                       prms.foldLeft ("") { case (acc, prm) => acc + printAST (prm) + ", " }
    case Resource (typ, insts) => typ + " " + "{" + "\n" +
                                  insts.foldLeft ("") { case (acc, inst) => acc + printAST (inst) + ";\n" } +
                                  "}"
    case ResourceDefaults (typ, prms) => printAST (typ) + " " + "{" + "\n"
                                         prms.foldLeft ("") { case (acc, prm) => acc + printAST (prm) + ", " }
                                         "}"
    case ResourceRef (typ, es) => printAST (typ) + " " + "[" +
                                  es.foldLeft ("") { case (acc, e) => acc + printAST (e) + ", " } + "]"
    case ResourceOverride (obj, prms) => printAST (obj) + " " + "{" + "\n" + 
                                         prms.foldLeft ("") { case (acc, prm) => acc + printAST (prm) + ",\n" } +
                                         "}"

    case VirtualResource (res, tvirt) => VirtualResTypeStr (tvirt) + printAST (res)
    case IfExpr (test, true_es, false_es) => "if" + " " + printAST (test) + " { " + printAST (true_es) + " } else { " + printAST (false_es) + "}\n"

    case CaseOpt (v, stmts) => v.foldLeft ("") { 
      case (acc, a) => acc + printAST (a) + ", " 
    } + ":" + " " + "{" + "\n" + printAST (stmts) + "}" + "\n"

    case CaseExpr (test, caseopts) => "case" + " " + printAST (test) + "{" + "\n"
                                      caseopts.foldLeft ("") { 
                                        case (acc, caseopt) => acc + printAST (caseopt) + " " 
                                      } + "}" + "\n"

    case Selector (prm, vs) => printAST (prm) + " " + "?" + " " + "{" + "\n"
                               vs.foldLeft ("") { case (acc, v) => acc + printAST (v) + ",\n" } +
                               "}"
    case CollectionExpr (lhs, rhs, op) => printAST (lhs) + " " + CollectionOpStr (op) + " " + printAST (rhs)

    case CollectionExprTagNode (None, prop) => if (prop == Vrtvirtual) "<| |>" else "<<| |>>"
    case CollectionExprTagNode (Some (coll), prop) => 
      if (prop == Vrtvirtual) ("<|" + " " + printAST (coll) + " " + "|>")
      else ("<<|" + " " + printAST (coll) + " " + "|>>")

    case Collection (typ, collectrhand, Nil) => printAST (typ) + " " + printAST (collectrhand)
    case Collection (typ, collectrhand, prms) => printAST (typ) + " " + printAST (collectrhand) + " " + "{" + "\n" +
    prms.foldLeft ("") { case (acc, prm) => acc + printAST (prm) + "," + "\n" } +
    "}" + "\n"

    case Hostclass (clnm, Nil, None, stmts) => "class" + " " + clnm + " " + "{" + "\n" + printAST (stmts) + "}" + "\n"
    case Hostclass (clnm, args, None, stmts) => "class" + " " + clnm + 
      " " + "(" + args.foldLeft ("") { 
        case (acc, (v, None)) => acc + v + ", "
        case (acc, (v, Some (e))) => acc + v + " = " + printAST (e)
       } + ")" + " " + "{" + "\n" + printAST (stmts) + "}" + "\n"
    case Hostclass (clnm, Nil, Some (parent), stmts) => "class" + " " + clnm + " " + "inherits" + " " + parent + "{" + "\n" + printAST (stmts) + "}" + "\n"
    case Hostclass (clnm, args, Some (parent), stmts) => "class" + " " + clnm + " " + "inherits" + " " + parent + " " + "(" + args.foldLeft ("") { 
        case (acc, (v, None)) => acc + v + ", "
        case (acc, (v, Some (e))) => acc + v + " = " + printAST (e) 
      } + ")" + " " + "{" + "\n" + printAST (stmts) + "}" + "\n"

    case Function (nm, args, _) => nm + " " + "(" + " " + 
      args.foldLeft ("") { case (acc, a) => acc + printAST (a) + ", " } + " " + ")"

    case Import (imps) => "import" + " " + imps.foldLeft ("") { case (acc, i) => acc + i + ", " } + "\n"

    case Node (hostnames, None, es) => "node" + " " + hostnames.foldLeft ("") {
      case (acc, hostname) => acc + printAST (hostname) + ", "
    } + " " + "{" + "\n" + printAST (es) + "}" + "\n"

    case Node (hostnames, Some (parent), es) => "node" + " " + hostnames.foldLeft ("") {
      case (acc, hostname) => acc + printAST (hostname) + ", "
    } + " " + "inherits" + " " + parent + " " + "{" + "\n" + printAST (es) + "}" + "\n"

    case Definition (classname, Nil, es) => "define" + " " + classname + " " + "{" + "\n" + printAST (es) + "}" + "\n"
    case Definition (classname, args, es) => "define" + " " + classname + " " + "(" + args.foldLeft ("") { 
        case (acc, (v, None)) => acc + v + ", "
        case (acc, (v, Some (e))) => acc + v + " = " + printAST (e) 
      } + 
      ")" + " " + "{" + "\n" + printAST (es) + "}" + "\n"
  }
}
