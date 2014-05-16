package puppet.driver

import puppet.parser._
import puppet.core._
import puppet.core.eval._

import scalax.collection.GraphEdge._
import scalax.collection.io.json._
import scalax.collection.io.json.descriptor.predefined._

object PuppetDriver {

  def apply (content: String) {
    val ast = PuppetParser (content)
    val desugared_ast = DesugarPuppetAST.desugarAST (ast)
    val g = 
      PuppetCompile.compile (desugared_ast.asInstanceOf[BlockStmtC]) match {
        case Left (l) => throw new Exception ("Not supported")
        case Right (catalog) => catalog.to_graph ()
      }

    val node_desc = new NodeDescriptor[Resource] (typeId = "Resources") {
      def id (node: Any): String = node match {
        case x: Resource  => "%s[%s]".format (x.kind, x.title)
      }
    }

    val quickJson = new Descriptor[Resource] (
      defaultNodeDescriptor = node_desc,
      defaultEdgeDescriptor = Di.descriptor ()
    )

    // println (g.toJson (quickJson))
  }
}
