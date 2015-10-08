package rehearsal

object Evaluator2 {

  import Syntax._
  import scalax.collection.mutable.Graph
  import scalax.collection.mutable.Graph._
  import scalax.collection.GraphEdge._

  // A directed graph of resource dependencies
  type ResourceGraph = Graph[Resource, DiEdge]
  // A map from string names to associated Class / Define type
  type Lookup = Map[String, Manifest]
  // A map from variable names to their assigned expression.
  type Store = Map[String, Expr]

  def eval(m: Manifest, g: ResourceGraph, s: Store, l: Lookup): (ResourceGraph, Store, Lookup) =
    m match {
      case Empty => (g, s, l)

      case Block(m0, m1) => {
        val (g0, s0, l0) = eval(m0, g, s, l)
        eval(m1, g0, s0, l0)
      }

      case r@Resource(_, _, _) => (g+r, s, l)

      //TODO(jcollard): Left / Right should reduce to resources
      case Edge(m1, m2) => {
        throw new Exception("not implemented")
      }

      case _ => throw new Exception()
    }

  def eval(m: Manifest): (ResourceGraph, Store, Lookup) =
    eval(m, Graph(), Map(), Map())

}
