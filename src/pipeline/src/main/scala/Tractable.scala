import scalax.collection.Graph
import scalax.collection.GraphEdge._

object ReduceDAG {

  private def is_ordered[N](u: N, v: N, tc: Set[(N, N)]): Boolean = {
    tc.exists({ case (a, b) => (a == u && b == v) || (a == v && b == u)})
  }

  private def check_commutativity[N](dag: Graph[N, DiEdge],
                                     commutes: (N,N) => Option[Boolean]): Set[(N, N)] = {

    import scala.collection.mutable.{Set => MSet}

    val (set, relation) = PartialOrderGlue.toPoset(dag)
    val tc = TransitiveClosure(relation)

    var unordered: MSet[(N, N)] = MSet.empty

    /* Check pairwise commutativity for all nodes.
     * If oracle says that they necessarily do not commute then there should be
     * an edge between the nodes. If the edge is missing then report error.
     */
    for(i <- set;
        j <- set if i != j) {

      commutes(i, j) match {

        case Some(true) => ()
        case Some(false) => /* there should exists edge between i & j, otherwise error out on missing edge */
                            if(!is_ordered(i, j, tc)) {
                              throw new Exception(s"Commutativity test failed: Edge missing between $i & $j")
                            }
        case None => /* Commutativity could not be determined
                      * If i & j are ordered in original dag then ignore as it will be checked by dynamic analysis
                      * If i & j are unordered in dag(part of antichain) then it should remain so, we should not
                      * order it ourselves.
                      */
                      if(!is_ordered(i, j, tc)) {
                        unordered += ((i, j))
                      }
      }
    }

    unordered.toSet
  }

  private def toBipartiteGraph[N](dag: Graph[N, DiEdge]): (Set[N], Set[N], Set[(N, N)]) = {
    // TODO : Duplicate poset and tc, see above. Refactor!
    val (set, relation) = PartialOrderGlue.toPoset(dag)
    val tc = TransitiveClosure(relation)
    (set, set, tc)
  }

  // function for set(N, N) to Map[Int, Seq[Int]]

  def apply[N](dag: Graph[N, DiEdge], commutes: (N,N)=>Option[Boolean]): Graph[N, DiEdge] = {

    // Check if dag has cycles? if yes then throw Exception
    if(dag.isCyclic) throw new Exception("Dag has cycles, cannot continue")

    // While linearizing chains, the chains containing unordered elements will not be linearized
    val unordered = check_commutativity(dag, commutes)

    val (u, v, e) = toBipartiteGraph(dag)

    val ui = u.zipWithIndex // Run only once as it might give different ordering since nodes are unordered(I think)
    val umap = ui.toMap // Map from Nodes to indices
    val urmap = ui.map({ case (e, i) => (i, e)}).toMap // Map from Indices to Nodes

    val vi = v.zipWithIndex
    val vmap = vi.toMap
    val vrmap = vi.map({ case (e, i) => (i, e)}).toMap
    
    val adj_lst = e.map({ case (l, r) => (umap(l), vmap(r)) })
                   .groupBy({ case (l, r) => l })
                   .mapValues((s) => s.unzip._2.toSeq)
  
    val matching = HopcroftKarp.findMaximalMatching(urmap.keySet.toSeq, vrmap.keySet.toSeq, adj_lst)

    /* TODO: 
     *   Trace chains from matching
     *   Linearize chains 
     */

     dag
  }
}
