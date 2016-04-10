package rehearsal

object DeterminismPruning extends com.typesafe.scalalogging.LazyLogging   {

  import FSSyntax._
  import Implicits._

  def pruneWrites(fsgraph: FSGraph): FSGraph = {
    logTime("Pruning writes") {
      val nodes = fsgraph.deps.topologicalSort.reverse
      nodes.foldLeft(fsgraph) {
        case (FSGraph(exprs, graph), nodeValue) => {
          val node = graph.get(nodeValue)
          val succs = graph.nodes.toSet -- graph.ancestors(node) - node
          val commutesAll = succs.forall { succ =>
            fsgraph.exprs(node.value).commutesWith(fsgraph.exprs(succ.value))
          }
          if (commutesAll) FSGraph(exprs - node, graph.shrink(node))
          else FSGraph(exprs, graph)
        }
      }
    }
  }
}
