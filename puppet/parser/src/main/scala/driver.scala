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
        case Right (catalog) => catalog.toGraph
      }

    val node_desc = new NodeDescriptor[Node] (typeId = "Resources") {
      def id (node: Any): String = node match {
        case x: Resource  => "Resource[%s]".format (x.title)
        case x: HostClass => "Class[%s]".format (x.title)
        case x: Stage     => "Stage[%s]".format (x.title)
      }
    }

    val quickJson = new Descriptor[Node] (
      defaultNodeDescriptor = node_desc,
      defaultEdgeDescriptor = Di.descriptor ()
    )

    // println (g.toJson (quickJson))
  }
}
