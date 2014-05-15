package puppet.core.eval

import puppet.core._
import scala.util.Try

// XXX: Imperative
object TypeCollection {

  import scala.collection.mutable._

  // mutable objects
  private val hostclasses = Map [String, HostclassC] ()
  private val definitions = Map [String, DefinitionC] ()

  private def hostclass_exists (classname: String): Boolean = {
    (Try (hostclasses (classname))).isSuccess
  }

  private def definition_exists (classname: String): Boolean = {
    (Try (definitions (classname))).isSuccess
  }

  def add (hc: HostclassC) {

    if (definition_exists (hc.classname)) throw new Exception ("Class by this name already exists")

    val merged = hostclasses.get (hc.classname) match {

      case Some (other_hc) => 
        if (other_hc.parent == hc.parent) HostclassC (hc.classname, hc.args, hc.parent, BlockStmtC (other_hc.stmts.asInstanceOf[BlockStmtC].exprs ::: hc.stmts.asInstanceOf[BlockStmtC].exprs))
        else throw new Exception ("Cannot merge two hostclasses inheriting different parents")

      case None => hc
    }

    hostclasses += (merged.classname -> merged)
  }

  def add (definition: DefinitionC) {

    if (definition_exists (definition.classname) || hostclass_exists (definition.classname))
      throw new Exception ("Duplicate definition, either a class or definition by this name already exists")
    
    definitions += (definition.classname -> definition)
  }
}
