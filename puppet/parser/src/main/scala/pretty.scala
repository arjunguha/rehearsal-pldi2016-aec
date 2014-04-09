import scala.collection.immutable.Map

object PrettyPrintAST {

  private val ArithOpMap = Map (Plus   -> "+",
                                Minus  -> "-",
                                Div    -> "/",
                                Mult   -> "*",
                                Mod    -> "%",
                                LShift -> "<<",
                                RShift -> ">>")

  private val BoolBinOpMap = Map (And -> "and", Or -> "or")

  private val CompareOpMap = Map (NotEqual    -> "!=",
                                  Equal       -> "==",
                                  GreaterThan -> ">",
                                  GreaterEq   -> ">=",
                                  LessThan    -> "<",
                                  LessEq      -> "<=")

  private val MatchOpMap = Map (Match -> "=~", NoMatch -> "!~")

  private val RelationOpMap = Map (LeftSimpleDep     -> "<-",
                                   RightSimpleDep    -> "->",
                                   LeftSubscribeDep  -> "<~",
                                   RightSubscribeDep -> "~>")

  private val CollectionOp = Map (CollOr    -> "or",
                                  CollAnd   -> "and",
                                  CollIsEq  -> "==",
                                  CollNotEq -> "!=")

  private val VirtualResTypeMap = Map (Vrtvirtual  -> "@",
                                       Vrtexported -> "@@")



  private def printLeaf (l: Leaf): String = {

    case ASTBool (b)              => printBool (b)
    case ASTString (s)            => s
    case Concat (lhs, rhs)        => printAst (lhs) + " " + printAST (rhs)
    case Default                  => "default"
    case Type (t)                 => t.value
    case Name (n)                 => n.value
    case Undef                    => "undef"
    case Hostname (h)             => h.value
    case Variable (v)             => v.value
    case HashOrArrayAccess (v, k) => printLeaf (v) + "[" + printAst (k) + "]"
    case ASTRegex (r)             => r.value
    case ASTHash (h)              => "{" + 
                                        h.kvs.foldLeft ("") { 
                                            case (acc, (leaf, ast)) => 
                                              acc + " " + printLeaf (leaf) + " => " printAst (ast) + ", "
                                            } +
                                      "}"
  }





  def printBranch (branch: Branch): String = {

    case BlockExpr (es) => es.foldLeft ("") { case (acc, ast) => printAst (ast) + "\n" }
    // TODO : Parentheses and precedence
    case ArithExpr (ae) => printAst (ae.lhs) + " " + ArithOpMap (ae.op) + " " + printAst (ae.rhs)
    case BoolBinExpr (be) => printAst (be.lhs) + " " + BoolBinOpMap (be.op) + " " + printAst (be.rhs)
    case CompareExpr (ce) => printAst (ce.lhs) + " " + CompareOpMap (ce.op) + " " + printAst (ce.rhs)
    case InExpr (ie) => printAst (ie.lhs) + " in " + printAst (ie.rhs)
    case RelationExpr (re) => printAst (re.lhs) + " " + RelationOpMap (re.op) + " " + printAst (re.rhs)
    case MatchExpr (me) => printAst (me.lhs) + " " + MatchOpMap (me.op) + " " + printAst (me.rhs)
    case NotExpr (ne) => "!" + printAst (ne)
    case UMinusExpr (ume) => "-" + printAst (ume)
    case Vardef (nm, v, is_append) => printLeaf (nm) + (if (is_append) " += " else " = ") + printAst (v)
    case ASTArray (arr) => "[" + 
                              arr.foldLeft ("") { case (acc, x) => acc + printAst (x) + ", "} +
                           "]"
    case ResourceParam (p, v, is_add) => printAst (param) + (if(is_add) " +> " else " => ") + printAst (v)
    case ResourceInstance (t, prms) => printAst (t) + ": " + 
                                       prms.foldLeft ("") { case (acc, prm) => acc + printBranch (prm) + ", " }
    case Resource (typ, insts) => typ + " " + "{" + "\n" +
                                  insts.foldLeft ("") { case (acc, inst) => acc + printBranch (inst) + ";\n" } +
                                  "}"
    case ResourceDefaults (typ, prms) => printLeaf (typ) + " " + "{" + "\n"
                                         prms.foldLeft ("") { case (acc, prm) => acc + printBranch (prm) + ", " }
                                         "}"
    case ResourceRef (typ, es) => printLeaf (typ) + " " + "[" +
                                  es.foldLeft ("") { case (acc, e) => acc + printAst (e) + ", " }
                                  + "]"
    case ResourceOverride (obj, prms) => printBranch (obj) + " " + "{" + "\n" + 
                                         prms.foldLeft ("") { case (acc, prm) => acc + printBranch (prm) + ",\n" } +
                                         "}"

    case VirtualResource (res, tvirt) => VirtualResTypeMap (tvirt) + printBranch (res)
    case IfExpr (test, true_es, false_es) => "if" + " " + printAst (test) + " { " printAst (tue_es) + " } else { " + printAst (false_es) + "}\n"
    case CaseOpt (v, stmts) => printAst (v) + ":" + " " + "{" + "\n"
                               printAst (stmts) + "}" + "\n"
    case CaseExpr (test, caseopts) => "case" + " " + printAst (test) + "{" + "\n"
                                      printBranch (caseopts) + "}" + "\n"
    case Selector (prm, vs) => printAst (prm) + " " + "?" + " " + "{" + "\n"
                               vs.foldLeft ("") { case (acc, v) => acc + printBranch (v) + ",\n" } +
                               "}"
    case CollectionExpr (lhs, rhs, op) => printAst (lhs) + " " + CollectionOp (op) + " " _ printAst (rhs)
    case CollectionExprTagNode (None, prop) => if (prop == Vrtvirtual) "<| |>" else "<<| |>>"
    case CollectionExprTageNode (Some (coll), prop) => 
      if (prop == Vrtvirtual) "<|" + " " + printBranch (coll) + " " + "|>"
      else "<<|" + " " + printBranch (coll) + " " + "|>>"

    case Collection (typ, collectrhand, Nil) => printLeaf (typ) + " " + printBranch (collectrhand)
    case Collection (typ, collectrhand, prms) => printLeaf (typ) + " " + printBranch (collectrhand) + " " + "{" + "\n" +
    prms.foldLeft ("") { case (acc, prm) => acc + printBranch (prm) + "," + "\n" } +
    "}" + "\n"

    case Hostclass (clnm, Nil, None, stmts) => "class" + " " + clnm + " " + "{" + "\n" + printAst (stmts) + "}" + "\n"
    case Hostclass (clnm, args, None, stmts) => "class" + " " + clnm + 
      " " + "(" + args.foldLeft ("") { 
        case (acc, (v, None)) => acc + printLeaf (v) + ", "
        case (acc, (v, Some (e))) => acc + printLeaf (v) + " = " + printAst (e)
       } + ")" + " " + "{" + "\n" + printAst (stmts) + "}" + "\n"
    case hostclass (clnm, Nil, Some (parent), stmts) => "class" + " " + clnm + " " + "inherits" + " " + printLeaf (parent) + "{" + "\n" + printAst (stmts) + "}" + "\n"
    case Hostclass (clnm, args, Some (parent), stmts) => "class" + " " + clnm + " " + "inherits" + " " + printLeaf (parent) + " " + "(" + args.foldLeft ("") { 
        case (acc, (v, None)) => acc + printLeaf (v) + ", "
        case (acc, (v, Some (e))) => acc + printLeaf (v) + " = " + printAst (e) 
      } + ")" + " " + "{" + "\n" + printAst (stmts) + "}" + "\n"

/*
    case class Function (nm, args, _) => nm + " " + "(" + " " + 
      args.foldLeft ("") { case (acc, a) => acc + printAst (a) + ", " } + " " + ")"

    case class Import (imps) => "import" + " " + imps.foldLeft ("") { case (acc, i) => acc + i + ", " } + "\n"
    */
}

  def printTopLevelConstruct (tlc: TopLevelConstruct): String = {
    
    case Node (hostnames, None, es) => "node" + " " + hostnames.foldLeft ("") {
      case (acc, hostname) => acc + printLeaf (hostname) + ", "
    } + " " + "{" + "\n" + printAst (es) + "}" + "\n"

    case Node (hostnames, Some (parent), es) => "node" + " " + hostnames.foldLeft ("") {
      case (acc, hostname) => acc + printLeaf (hostname) + ", "
    } + " " + "inherits" + " " + parent + " " + "{" + "\n" + printAst (es) + "}" + "\n"

    case Definition (classname, Nil, es) => "define" + " " + classname + " " + "{" + "\n" + printAst (es) + "}" + "\n"
    case Definition (classname, args, es) => "define" + " " + classname + " " + "(" + args.foldLeft ("") { 
        case (acc, (v, None)) => acc + printLeaf (v) + ", "
        case (acc, (v, Some (e))) => acc + printLeaf (v) + " = " + printAst (e) 
      } + 
      ")" + " " + "{" + "\n" + printAst (es) + "}" + "\n"
  }

                            
  def printAst (ast: AST): String = {

    case Leaf => printLeaf (ast)
    case Branch => printBranch (ast)
    case TopLevelConstruct => printTopLevelConstruct (ast) 
  }
}
