import scalax.collection.Graph
import scalax.collection.GraphEdge.DiEdge

package object eval {

    type FileScriptGraph = Graph[Expr, DiEdge]

}