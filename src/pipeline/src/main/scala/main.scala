package pipeline

import puppet.syntax._
import puppet.graph._

import puppet.common.{resource => resrc}

import scalax.collection.Graph
import scalax.collection.GraphEdge._
import scalax.collection.GraphPredef._
import scalax.collection.edge.Implicits._

import eval._
import eval.Implicits._

package object pipeline {

  def resourceGraphToExpr(resourceGraph: Graph[puppet.graph.Resource, DiEdge]): eval.Expr = {
    val toExpr = toCoreResource _ andThen { Provider(_).toFSOps() }
    reduceGraph(resourceGraph, toExpr)
  }

  type State = Ample.State

  def run(mainFile: String, modulePath: Option[String],
          env: Map[String, String],
          fs: State): Int = {
    runProgram(load(mainFile, modulePath), env, fs)
  }

  def runProgram(program: String,
                 env: Map[String, String],
                 fs: State): Int = {

    val graph = parse(program).desugar()
                              .toGraph(env)

    val expr = resourceGraphToExpr(graph)

    0
  }

  // Reduce the graph to a single expression in fsmodel language
  def reduceGraph[A](graph: Graph[A, DiEdge], toExpr: A=>eval.Expr): eval.Expr = {

    import scala.annotation.tailrec

    @tailrec
    def loop(graph: Graph[A, DiEdge], acc: eval.Expr): eval.Expr =
      if(graph.isEmpty) acc
      else {
        val roots = graph.nodes.filter(_.inDegree == 0)
        loop(graph -- roots,
             acc >> roots.map((n) => Atomic(toExpr(n.value)))
                         .reduce[eval.Expr](_ * _))
      }

    loop(graph, Skip)
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
}
