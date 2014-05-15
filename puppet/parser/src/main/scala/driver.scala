package puppet.driver

import puppet.parser._
import puppet.core._

// Hacked up for smoke testing

object PuppetDriver {

  def apply (content: String) {
    val ast = PuppetParser (content)
    val desugared_ast = DesugarPuppetAST.desugarAST (ast)
    eval.PuppetCompile.compile (desugared_ast.asInstanceOf[BlockStmtC]).right.map (_.to_graph ())
  }
}
