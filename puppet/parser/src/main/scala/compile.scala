package puppet;

import scala.collection.mutable.HashMap

// Understand puppet catalog production from AST
// Understand scoping issues
// See evaluation rules for nodes


// TODO : Collection of puppet pre-defined functions
/*
object <funcname> {

  def apply (args): PuppetValue {

  }
}
*/


object PuppetCompile {

  sealed abstract trait PuppetValue

  type ValueHashMap = HashMap[PuppetValue, PuppetValue]
  type ValueArray   = Array[PuppetValue]

  case object UndefV extends PuppetValue
  case class BoolV (value: Boolean) extends PuppetValue
  case class StringV (value: String) extends PuppetValue
  case class RegexV (value: Regex) extends PuppetValue
  case class ASTHashV (value: ValueHashMap) extends PuppetValue
  case class ASTArrayV (value: ValueArray) extends PuppetValue
  /* TODO : Resource should be a value
   * case class ResourceV (value: 
   */

    /*
     * Properties of scopes
     *
     * The following kind of scopes are possible in puppet
     *
     * 1) Top level scope
     * 2) Node level scope
     * 3) Parent Scope
     * 4) Local Scope
     * 
     * Every Scope has only one parent
     *
     * Class definition creates a named scope whose name is the same as the class's name
     * 
     * Top scope is a named scope
     *
     * Node scope and local scopes created by defined resources and anonymous and cannot
     * be directly refrenced
     *
     * REFERENCING OUT OF SCOPE VARIABLES
     * Variables declared in named scopes can be referenced directly from anywhere 
     * (Including scopes hat otherwise would not have access to them) by using their
     * global qualified name.
     * Out of scope variables are available in other scopes subject to their declaration
     * (Parse order dependence)
     *
     * Variables declared in anonymous scopes can only be accessed normally and do not
     * have global qualified names.
     *
     * Parent scope is only assigned by class inheritance (using the inherits keyword)
     * Any derived class receives the contents of its base class in addition to the 
     * contents of node and top scope
     *
     * Nodes can be inherited similar to classes and similar scope inheritance rules
     * apply to them as well.
     *
     * Appending to any variable referenced from outside the local scope would be
     * treated as a new variable definition in current scope 
     */

    type Env = Map[String, PuppetValue]

    // Named scopes

    // Special name: __toplevel__, __node__
    type ScopeName = String
    val toplevel: ScopeName  = "__toplevel__"

    val named_scopes = Map [ScopeName, Env] ()

    type ScopeChain = List[ScopeName]


    def init_scope () {

      val facter_env = Cmd.exec ("facter").get
      val env = Env ()
      facter_env.lines.foreach ({ val  = _.split ("=>").foreach (_.trim)

    }

    def add_new_scope (val name: ScopeName,
                       val env: Env = new Env ()): Env = named_scopes += (name, env); env
    }

    

  private def puppetvalue_to_bool (v: PuppetValue): Boolean = v match {

    /* Puppets idiosyncracies on what can be (automatically) coerced
     * into a bool
     */
    case UndefV => false
    case BoolV (b) => b
    case StringV (s) => ! (s == "" || s == "\"\"" || s == "''") // Empty strings are false
    case RegexV => throw new Exception ("Cannot convert a regex to bool")
    case ASTHashV (_) | ASTArrayV (_) => true // Any hash or array, even empty ones are boolean true
  }

  import scala.util.Try
   
  private def puppetvalue_to_double (v: PuppetValue): Try[Double] = v match {
    case StringV (s) => Try (s.toDouble)
    case _ => throw new Exception ("Cannot convert to double")
  }
  
  private def puppetvalue_to_int (v: PuppetValue): Try[Int] = v match {
    case StringV (s) => Try (s.ToInt) // TODO: Not supporting hex and octal for now 
    case _ => throw new Exception ("Cannot convert to Integer")
  }

  import scala.util.Either
  private def puppetvalue_to_num (v: PuppetValue): Either [Double, Int] = {

    // Cases : Octal, Hexadecimal, Decimal (Negative, Positive), Double (Scientific, negative, positive)
    // First try to parse Octal, if it fails then hex then decimal else double
    val n = puppetalue_to_int (v)
    if (n.isSuccess) Right (n.get) else Left (puppetvalue_to_double (v).get)
  }


  // 
  private def eval_op (lhs: PuppetValue,
                       rhs: PuppetValue,
                       op: BinOp): PuppetValue = op match {


    // Takes in boolean operands or operands that can be converted to boolean
    case Or          => BoolV (puppetvalue_to_bool (lhs) || puppetvalue_to_bool (rhs))
    case And         => BoolV (puppetvalue_to_bool (lhs) && puppetvalue_to_bool (rhs))

    // XXX: All integer related operations have to follow ruby semantics and its flexibility/limitations

    // comparison operators: takes operands of several data types and resolve to Boolean
    case GreaterThan => {
      val lhsn = puppetvalue_to_num (lhs)
      val rhsn = puppetvalue_to_num (rhs)
      BoolV (lhsn > rhsn)
    }
    case GreaterEq   => {
      val lhsn = puppetvalue_to_num (lhs)
      val rhsn = puppetvalue_to_num (rhs)
      BoolV (lhsn >= rhsn)
    }

    case LessThan    => {
      val lhsn = puppetvalue_to_num (lhs)
      val rhsn = puppetvalue_to_num (rhs)
      BoolV (lhsn < rhsn)
    }

    case LessEq      => {
      val lhsn = puppetvalue_to_num (lhs)
      val rhsn = puppetvalue_to_num (rhs)
      BoolV (lhsn <= rhsn)
    }  

    // TODO : Define equality
    case NotEqual    =>
    case Equal       =>

    // Arithmetic operators, Takes in numbers and resolve to Numbers
    case LShift      => {
      val lhsn = puppetvalue_to_num (lhs)
      val rhsn = puppetvalue_to_num (rhs)

      /*
       * Being ruby compliant, when we ask for left shift by a negative
       * number, ruby does a right shift by its absolute value
       */
      if (rhsn < 0) lhsn >> Math.abs (rhsn)
      else lhsn << rhsn
    }

    case RShift      => {
      val lhsn = puppetvalue_to_num (lhs)
      val rhsn = puppetvalue_to_num (rhs)

      /* Being ruby compliant, when we ask for right shift by a negative
       * number, ruby does a right shift by its absolute value
       */
      if (rhsn < 0) lhsn << Math.abs (rhsn)
      else lhsn >> rhsn
    }

    case Plus        => {
      val lhsn = puppetvalue_to_num (lhs)
      val rhsn = puppetvalue_to_num (rhs)
      
      lhsn + rhsn
    }

    case Minus       => {
      val lhsn = puppetvalue_to_num (lhs)
      val rhsn = puppetvalue_to_num (rhs)

      lhsn - rhsn
    }

    case Div         => {
      val lhsn = puppetvalue_to_num (lhs)
      val rhsn = puppetvalue_to_num (rhs)

      lhsn / rhsn
    }

    case Mult        => {
      val lhsn = puppetvalue_to_num (lhs)
      val rhsn = puppetvalue_to_num (rhs)

      lhsn * rhsn
    }

    case Mod         => {
      val lhsn = puppetvalue_to_num (lhs)
      val rhsn = puppetvalue_to_num (rhs)

      lhsn % rhsn
    }


    // Regex related match, string is left operand and regular expression as right operand, returns a boolean
    case Match       => {
      val lhsstr   = puppetval_to_string (lhs)
      val rhsregex = puppetal_to_regex (rhs)

      // Check for any match
      rhsregex.findFirstIn (lhsstr) match {
        case Some (_) => BoolV (false)
        case None     => BoolV (true)
      }
    }

    case NoMatch     => {
      val lhsstr   = puppetval_to_string (lhs)
      val rhsregex = puppetal_to_regex (rhs)

      // Check for any match
      rhsregex.findFirstIn (lhsstr) match {
        case Some (_) => BoolV (false)
        case None     => BoolV (true)
      }
    }

    case In          => {

      // lhs has to be a string
      lhsstr = puppetval_to_string (lhs)

      // rhs could be either a String, Array or Hashes
      rhs match {
        case StringV (value) => /* Check if lhsstr is a substring */ BoolV (value contains lhsstr)
        case ASTArrayV (arr) => /* Check if any array element is identical to left operand */ BoolV (arr contains lhs)
        case ASTHashV (hash) => /* Check if any key is identical to left operand */ BoolV (hash contains lhs)

        // TODO : Position in error
        case _ => throw new Exception ("Type error: \"in\" expects a string, array or hash")
      }
    }
  }


  private def interpolate (str: String,
                           env: Environment): String = {
    // TODO
    // See puppet interpolation
    throw new Exception ("YTD")
  }
    
  private def eval (ast: ASTCore, env: Environment): PuppetValue = ast match {

    case UndefC          => UndefV
    case BoolC (value)   => BoolV (value)
    case StringC (value) => StringV (interpolate (value))
    case TypeC (value)   => StringV (value) // XXX: Not sure
    case NameC (value)   => StringV (value) // XXX: Not sure
    case RegexC (value)  => RegexV (Regex (value.r))

    case ASTHashC (kvs) => {
      var hashmap = new ValueHashMap ()
      kvs.foreach ({ case (k, v) => hashmap ++ (eval (k, env), eval (v, env))})
      ASTHashV (hashmap)
    }

    case ASTArrayC (arr) => ASTArrayV (arr.map (eval (_, env)).toArray)
    case HashOrArrayAccessC (variable, keys) => /* lookup variable and apply key */
    case VariableC (value) => /* lookup variable and apply key */
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
    // TODO : First preprocess to known resource types: Node, Class, Define, ResourceS?
    // Then start evaluating nodes in AST along with their scopes
  }
}
