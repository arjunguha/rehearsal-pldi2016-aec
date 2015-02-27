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

  def resourceGraphToExpr(resourceGraph: Graph[puppet.graph.Resource, DiEdge]): ext.Expr = {
    val toExpr = toCoreResource _ andThen { Provider(_).toFSOps() }
    reduceGraph(resourceGraph, toExpr)
  }

  type State = core.Eval.State

  def run(mainFile: String, modulePath: Option[String], fs_state: State): Int = {
    runProgram(load(mainFile, modulePath), fs_state)
  }

  def runProgram(program: String, fs_state: State): Int = {

    import fsmodel.core._

    val graph = parse(program).desugar()
                              .toGraph(Facter.run())

    val ext_expr = resourceGraphToExpr(graph)

    // TODO(nimish): debug only
    val simple_expr = ext_expr.unconcur()
                              .unatomic()

    val opt_expr = ext_expr.unconcurOpt()
                           .unatomic()

    val states = Eval.eval(opt_expr.toCore(), fs_state).toSet

    // TODO(nimish): debug only
    if(states.size != 1) {
      printDOTGraph(graph)
      println()
      println(ext_expr.pretty())
      println()
      println(simple_expr.pretty())
      println()
      println(opt_expr.pretty())
      println()
      println()
      println()
    }

    states.size
  }

  // Reduce the graph to a single expression in fsmodel language
  def reduceGraph[A](graph: Graph[A, DiEdge], toExpr: A=>ext.Expr): ext.Expr = {

    import fsmodel.ext.Implicits._
    import scala.annotation.tailrec

    @tailrec
    def loop(graph: Graph[A, DiEdge], acc: ext.Expr): ext.Expr =
      if(graph.isEmpty) Skip
      else {
        val roots = graph.nodes.filter(_.inDegree == 0)
        loop(graph -- roots,
             acc >> roots.map((n) => Atomic(toExpr(n.value)))
                         .reduce[ext.Expr](_ * _))
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
