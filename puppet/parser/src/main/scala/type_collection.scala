package puppet.core.eval

import puppet.core._
import scala.util.Try

// XXX: Imperative
object TypeCollection {

  import scala.collection.mutable._

  // mutable objects
  private val hostclasses = scala.collection.mutable.Map [String, HostclassC] ()
  private val definitions = scala.collection.mutable.Map [String, DefinitionC] ()

  private def hostclass_exists (classname: String): Boolean = {
    ! (hostclasses get classname).isEmpty
  }

  private def definition_exists (classname: String): Boolean = {
    ! (definitions get classname).isEmpty
  }

  private def mergeHostclass (lhs: HostclassC, rhs: HostclassC): HostclassC = {

    if (lhs.parent == rhs.parent) 
      HostclassC (lhs.classname, lhs.args, lhs.parent, BlockStmtC (rhs.stmts.asInstanceOf[BlockStmtC].exprs ::: lhs.stmts.asInstanceOf[BlockStmtC].exprs))
    else 
      throw new Exception ("Cannot merge two hostclasses inheriting different parents")
  }

  def add (hc: HostclassC) {

    if (definition_exists (hc.classname)) 
      throw new Exception ("Class by this name already exists")

    val merged = (getClass (hc.classname)) map (mergeHostclass (_, hc)) getOrElse hc
    hostclasses += (merged.classname -> merged)
  }

  def add (definition: DefinitionC) {

    if (definition_exists (definition.classname) || hostclass_exists (definition.classname))
      throw new Exception ("Duplicate definition, either a class or definition by this name already exists")
    
    definitions += (definition.classname -> definition)
  }

  def getClass (name: String): Option[HostclassC] = hostclasses get name
}
