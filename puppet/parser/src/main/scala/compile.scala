package puppet;

import scala.collection._

// Understand puppet catalog production from AST
// Understand scoping issues
// See evaluation rules for nodes



object /*<funcname>*/ {

  def apply (/*args*/): PuppetValue {
  }
}

// TODO : Check scoping rules in puppet, scoping in puppet is confusing
object PuppetCompile {

  sealed abstract trait PuppetValue

  case object UndefV extends PuppetValue
  case class BoolV (value: Boolean) extends PuppetValue
  case class StringV (value: String) extends PuppetValue
  case class NumV (value: Double) extends PuppetValue
  case class RegexV (value: Regex) extends PuppetValue
  case class ASTHash (value: Map[Value, Value]) extends PuppetValue
  case class ASTArray (value: Array[Value]) extends PuppetValue

  // Seems puppet uses dynamic scoping at some places and 
  private object Environment {

    def init () {
      // Facter to map
    }
  }


  private def puppetvalue_to_bool (v: PuppetValue): Boolean = { throw new Exception ("YTD") }

  private def eval_op (lhs: PuppetValue,
                       rhs: PuppetValue,
                       op: BinOp): PuppetValue = op match {

   case Or          =>
   case And         =>
   case GreaterThan =>
   case GreaterEq   =>
   case LessThan    =>
   case LessEq      =>
   case NotEqual    =>
   case Equal       =>
   case LShift      =>
   case RShift      =>
   case Plus        =>
   case Minus       =>
   case Div         =>
   case Mult        =>
   case Mod         =>
   case Match       =>
   case NoMatch     =>
   case In          =>
  }


  private def interpolate (str: StringC): StringC = { throw new Exception ("YTD") }
    
 

  private def eval (ast: ASTCore, env: Environment): PuppetValue = ast match {

    case UndefC => UndefV
    case BoolC (value) => BoolV (value)
    case StringC (value) => // TODO : Interpolate
    case TypeC (value) =>
    case NameC (value) =>
    case RegexC (value) =>
    case ASTHashC (kvs) =>
    case ASTArrayC (arr) =>
    case HashOrArrayAccessC (variable, keys) =>
    case VariableC (value) =>
    case BlockStmtC (exprs) =>
    case IfElseC (test, true_br, false_br) =>
    case BinExprC (lhs, rhs, op) => eval_op (eval (lhs), eval (rhs), op)
    case NotExprC (oper) => BoolV (! puppetvalue_to_bool (eval (oper)))
    case FuncAppC (name, args) => /* TODO : lookup predefined set of functions */
    case ImportC (imports) =>
    case VardefC (variable, value, append) =>
    case OrderResourceC (source, target, refresh) =>
    case AttributeC (name, value, is_append) =>
    case ResourceDeclC (attrs) =>
    case ResourceRefC (filter) =>
    case ResourceOverrideC (ref, attrs) =>
    case NodeC (hostnames, parent, stmts) =>
    case HostclassC (classname, args, parent, stmts) =>
    case DefinitionC (classname, args, stmts) =>
  }


  def to_catalog (ast: ASTCore): /* some Graph type */ {

  }
}
