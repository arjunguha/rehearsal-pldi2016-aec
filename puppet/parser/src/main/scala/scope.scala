package puppet.core.eval

import scala.collection._
import scala.util.Try
import scala.util.Random

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


// TODO : Make it a class
object PuppetScope {

  type ScopeRef = String

  private class Scope {

    private val env = scala.collection.mutable.Map[String, Value] ()

    def setvar (varname: String, value: Value) = env += (varname -> value)
    def getvar (varname: String): Value = env (varname)
  }

  private val named_scopes = scala.collection.mutable.Map [ScopeRef, Scope] ()

  def scope_exists (name: String): Boolean = named_scopes contains name

  def createNamedScope (name: String): ScopeRef = {

    if (scope_exists (name))
      throw new Exception ("Scope by this name already exists")

    named_scopes += (name -> new Scope ())
    name
  }

  // XXX: Need not mix ephemeral scopes with named scopes
  def createEphemeralScope (): ScopeRef = {

    // alphanumeric random string
    val name = Random.alphanumeric.take (8).mkString
    if (scope_exists (name)) createEphemeralScope ()
    else {
      named_scopes += (name -> new Scope ())
      name
    }
  }

  private def getScopeByName (name: String): Try[Scope] = Try (named_scopes (name))

  def setvar (ref: ScopeRef, varname: String, value: Value) {

    var scope = getScopeByName (ref)

    if (scope.isSuccess) scope.map (_.setvar (varname, value))
    else throw new Exception ("Invalid Scope")
  }

  def getvar (ref: ScopeRef, varname: String): Try[Value] = {

    var scope = getScopeByName (ref)

    if (scope.isSuccess) scope.map (_.getvar (varname))
    else throw new Exception ("Invalid Scope")
  }

  // TODO: Should go away when we have made this object a class
  def clear () = {
    named_scopes.clear ()
  }
}



class ScopeChain (val scopes: List[PuppetScope.ScopeRef] = List[PuppetScope.ScopeRef] ()) {

  private def is_qualified (name: String): Boolean = ((name indexOf "::") > 0)

  def getvar (varfqname: String): Try[Value] = {

    if (is_qualified (varfqname)) {

      // Make sure that scopes are valid
      val tokens = (varfqname split "::")
      val scoperefs = tokens.slice (0, tokens.length - 1)
      val varname = tokens (tokens.length - 1)

      if (!scoperefs.forall (PuppetScope.scope_exists))
        throw new Exception ("Invalid scope chain")

      // the last one is variable name, all others are scope names
      PuppetScope.getvar (scoperefs (scoperefs.length - 1), varname)
    }
    else {

      // Order is important
      val foundscope = scopes.find (PuppetScope.getvar (_, varfqname).isSuccess)
      if (!foundscope.isEmpty)
         PuppetScope.getvar (foundscope.get, varfqname)
      else
         Try (throw new Exception ("Variable not found in any scope"))
    }
  }

  def setvar (varfqname: String, value: Value, append: Boolean = false) {

    // Variable can only be assigned using their short name
    if (!append && is_qualified (varfqname))
      throw new Exception ("Cannot assign a fully qualified variable")

    val cur_scope = scopes.head

    if (append) {

      val old_val = getvar (varfqname)

      if (!old_val.isSuccess)
        throw new Exception ("Cannot append to non existing variable")

      // Replace by append in Value
      val new_val = (old_val.get, value) match {
        case (StringV (ov), StringV (nv)) => StringV (ov + nv)
        case (ASTHashV (ov), ASTHashV (nv)) => ASTHashV ((ov.toList ++ nv.toList).toMap)
        case (ASTArrayV (ov), ASTArrayV (nv)) => ASTArrayV (ov ++ nv)
        case _ => throw new Exception ("Type mismatch for append")
      }
    }
    else {

      if (PuppetScope.getvar (cur_scope, varfqname).isSuccess)
        throw new Exception ("Cannot reassign variable")

      PuppetScope.setvar (cur_scope, varfqname, value)
    }
  }

  def addScope (scoperef: PuppetScope.ScopeRef): ScopeChain = {
    new ScopeChain (scoperef :: scopes)
  }
}
