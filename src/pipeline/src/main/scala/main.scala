package pipeline

import puppet.syntax._
import puppet.graph._

import puppet.common.{resource => resrc}

import scalax.collection.Graph
import scalax.collection.GraphEdge._
import scalax.collection.GraphPredef._
import scalax.collection.edge.Implicits._

import fsmodel._
import fsmodel.ext._

package object pipeline {

  def run(mainFile: String, modulePath: Option[String] = None) {
    runProgram(load(mainFile, modulePath))
  }

  def runProgram(program: String) {

    import fsmodel.core._
    import java.nio.file.Paths

    val graph = parse(program).desugar()
                              .toGraph(Facter.run())
    printDOTGraph(graph)

    val fsops_graph = mapGraph(toSerializable(graph),
                               {(r: resrc.Resource) => Provider(r).toFSOps()})
    val ext_expr = toFSExpr(fsops_graph)
    println(ext_expr.pretty())
    
    val simple_expr = ext_expr.unconcur()
                              .unatomic()
    println(simple_expr.pretty())   
    println()

    val opt_expr = ext_expr.unconcurOpt()
                           .unatomic()
    println(opt_expr.pretty())

    val init_state = Map(Paths.get("/") -> IsDir)
    val states = Eval.eval(opt_expr.toCore(), init_state)

    println(s"The given expression can result in ${states.size} final states")
  }

  // Reduce the graph to a single expression in fsmodel language
  def toFSExpr(graph: Graph[ext.Expr, DiEdge]): ext.Expr = {
    
    import fsmodel.ext.Implicits._
    
    if(graph.isEmpty) Skip
    else {
      val n = graph.nodes.filter(_.inDegree == 0)
      n.foldLeft(Skip: ext.Expr)((acc, x) => acc*Atomic(x.value)) >> toFSExpr(graph -- n)
    }
  }

  import scala.reflect.runtime.universe.TypeTag

  def mapGraph[A,B](graph: Graph[A, DiEdge], f: A=>B)
                   (implicit tt: TypeTag[DiEdge[B]]): Graph[B, DiEdge] = {

    Graph.from(graph.nodes.map((n) => f(n.value)),
               graph.edges.map((e) => f(e.source.value) ~> f(e.target.value)))
  }

  def toCoreValue(v: Value): resrc.Value = v match {
    case UndefV => resrc.UndefV
    case StringV(s) => resrc.StringV(s)
    case BoolV(b) => resrc.BoolV(b)
    case RegexV(_) => resrc.UndefV
    case ASTHashV(_) => resrc.UndefV
    case ASTArrayV(arr) => resrc.ArrayV(arr.map(toCoreValue(_))) 
    case ResourceRefV(_, _, _) => resrc.UndefV
  }

  def toCoreResource(res: puppet.graph.Resource): resrc.Resource = {
    // Rules to convert to core resource
    val attrs = res.as.filter((a) => a.value match {
      case UndefV | StringV(_) | BoolV(_) | ASTArrayV(_) => true
      case _ => false
    })
    .map((a) => (a.name, toCoreValue(a.value))).toMap

    resrc.Resource(attrs)
  }

  def toSerializable(g: Graph[puppet.graph.Resource, DiEdge]): Graph[resrc.Resource, DiEdge] = {
    // Convert to serializable Graph
    val nodes = g.nodes map ((n) => toCoreResource(n.value))
    val edges = g.edges map ((e) => toCoreResource(e.source.value) ~> toCoreResource(e.target.value))
    Graph.from(nodes, edges)
  }
}
