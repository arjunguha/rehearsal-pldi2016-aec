package puppet.driver

import puppet.parser._
import puppet.core._
import puppet.core.eval._

import puppet.runtime.core._
import puppet.runtime.toposortperm._

import scala.util.Try
import plasma.docker._

import scalax.collection.GraphEdge._
import scalax.collection.io.json._
import scalax.collection.io.json.descriptor.predefined._

object PuppetDriver {

  /*
  // TODO : Should come from configuration file
  private val url = "http://localhost:4243"

  private def createDockerContainer(dckr: Docker): CreateContainerResponse = {
    val cfg = docker.container("puppet-installer").copy(ExposedPorts = ("8140"->Some

  }
  */

  def apply (content: String) {
    val ast = PuppetParser (content)
    val desugared_ast = DesugarPuppetAST.desugarAST (ast)
    val g = 
      PuppetCompile.compile(desugared_ast.asInstanceOf[BlockStmtC]) match {
        case Left (l) => throw new Exception ("Not supported")
        case Right (catalog) => catalog.toGraph
      }

    if (g.isCyclic) {
      throw new Exception("Compiled graph contains a cycle")
    }

    // val dockerCfg = new Docker(url)
    val permutations = GraphTopoSortPermutations(g)

    /*
     * for every permuation
     *  create a container (and wait for it to reply to "ping"
     *   for every process builder 
     *     Send it for execution and wait for result
     */

    /*
    // TODO: Could be done in parallel for the number of permutations
    for(permutation <- perms
        
        // container <- docker.createContainer(cfg)
        resource <- permutation
        provider <- Provider(resource)) yield DockerInstall(provider, container)
    */

    val resource_desc = new NodeDescriptor[Resource] (typeId = "Resources") {
      def id (node: Any): String = node match {
        case x: Resource  => "Resource[%s]".format(x.title)
      }
    }

    val quickJson = new Descriptor[Resource](
      defaultNodeDescriptor = resource_desc,
      defaultEdgeDescriptor = Di.descriptor[Resource]()
    )

    println (g.toJson (quickJson))
  }
}
