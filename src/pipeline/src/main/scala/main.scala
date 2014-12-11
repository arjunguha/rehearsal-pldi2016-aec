package pipeline.main

import puppet.common._
import puppet.core.eval._
import puppet.common.toposortperm._
import equiv.sat._
import equiv.ast._
import equiv.desugar._
import equiv.semantics._

import puppet.driver.{PuppetDriver => driver}

import scala.collection.mutable

import scala.collection.immutable.HashMap
import scala.collection.mutable.{HashMap => MHashMap}

import scalax.collection.Graph
import scalax.collection.GraphEdge._
import scalax.collection.GraphPredef._
import scalax.collection.edge.LDiEdge // labelled directed edge
import scalax.collection.edge.Implicits._


case class ResourceLabel(r: Resource)
case class FSKATExprLabel(expr: FSKATExpr)

import scalax.collection.edge.LBase.LEdgeImplicits
object RImplicit extends LEdgeImplicits[ResourceLabel]
object FSKATImplicit extends LEdgeImplicits[FSKATExprLabel]


object Pipeline {

  import scalax.collection.mutable.{Graph => MGraph}

  private def DFAtoDot(dfa: Graph[Symbol, LDiEdge]): String = {

    import scalax.collection.io.dot._
    import scala.language.existentials

    val root = DotRootGraph(
      directed = true,
      id = Some("DFA"),
      kvList = Seq[DotAttr]())

    def edgeTransformer(innerEdge: Graph[Symbol, LDiEdge]#EdgeT):
      Option[(DotGraph, DotEdgeStmt)] = {
        val edge = innerEdge.edge
        val label = edge.label.asInstanceOf[ResourceLabel]
        Some((root,
              DotEdgeStmt(edge.from.value.name,
                          edge.to.value.name,
                          List(DotAttr("label", label.r.title))
                          )))
      }
      dfa.toDot(root, edgeTransformer)
  }


  def DFAtoRegExpr(dfa: Graph[Symbol, LDiEdge]): FSKATExpr = {
    val mdfa = MGraph.from(dfa.nodes.map(_.value),
                           dfa.edges.map(e => LDiEdge(e.source.value, e.target.value)(e.label)))
    DFAtoRegExpr(mdfa)
  }


  private def DFAtoRegExpr(dfa: MGraph[Symbol, LDiEdge]): FSKATExpr = {

    import FSKATImplicit._

    /*
     * CONVERT(dfa)
     * 1. Let k be the number of states of G
     * 2. If k = 2, then G must consist of a start state, an accept state, and a single
     *    arrow connecting them and labeled with a regular expression R
     *    Return the expression R
     * 3. If k > 2, we select any state Qrip (belonging to Q) different from Qstart and
     *    Qaccept and let G' be the GNFA (Q', Sigma, d', Qstart, Qaccept), where
     *         Q' = Q - {Qrip}
     * and for any Qi belonging to Q' - {Qaccept} and and Qj belonging to Q' - {Qstart} let
     *         d'(Qi, Qj) = (R1)(R2)*(R3) U (R4)
     * for R1 = d(Qi, Qrip), R2 = d(Qrip, Qrip), R3 = d(Qrip, Qj) and R4 = d(Qi, Qj)
     * 4. Compute CONVERT(G') and return this value
     */

     if (dfa.nodes.size == 2) {
       dfa.edges.seq.map(e=>e.label.expr).reduce(Opt)
     }
     else {

       val Qinit = dfa.nodes.find(_.inDegree == 0) getOrElse
                     (throw new Exception ("Qinit not found"))
       val Qaccept = dfa.nodes.find(_.outDegree == 0) getOrElse
                       (throw new Exception ("Qaccept not found"))

       val state = dfa.nodes.filter(n => n != Qinit && n != Qaccept).head

       val in_edges = state.incoming
       val out_edges = state.outgoing

       for (ie <- in_edges; oe <- out_edges) {

         val Qi = ie.source
         val Qj = oe.target

         val R1 = ie.label.expr
         val R3 = oe.label.expr

         val Eij = Qj.connectionsWith(Qi)
         val DQij = Eij.seq.foldLeft(Seqn(R1, R3): FSKATExpr)((acc, e) => Opt(acc, e.label.expr))

         dfa.add(LDiEdge(Qi.value, Qj.value)(FSKATExprLabel(DQij)))
       }

       // Could not get types to match (ie.value/ie.edge) therefore recreating edge
       in_edges.foreach(e=>dfa.remove(LDiEdge(e.source.value, state.value)(e.label)))
       out_edges.foreach(e=>dfa.remove(LDiEdge(state.value, e.target.value)(e.label)))
       dfa.remove(state.value)
       DFAtoRegExpr(dfa)
     }
  }

  private def labelstoFSKATExpr (dfa: Graph[Symbol, LDiEdge]): Graph[Symbol, LDiEdge] = {

    import RImplicit._

    Graph.from(dfa.nodes.map(_.value),
               dfa.edges.map(e=> {
                 val resource = driver.toCoreResource(e.label.r)
                 val kat_expr = Desugar(Provider(resource).toFSOps)
                 LDiEdge(e.source.value, e.target.value)(FSKATExprLabel(kat_expr))
               }))
  }

  import scala.reflect.runtime.universe.TypeTag

  private def DAGtoDFA[N](dag: Graph[N, DiEdge])
                         (implicit tt: TypeTag[DiEdge[Set[N]]]): Graph[Symbol, LDiEdge] = {

    var id = 0

    // Construct dfa with labelled edges
    def grunt(dfa: MGraph[Symbol, LDiEdge], level: Map[Set[N], Symbol]) {

      val nextlevel = MHashMap.empty[Set[N], Symbol]

      level foreach { case (set, src_symb) => {
        val tmpgraph = MGraph.from(dag.nodes.map(_.value),
                                   dag.edges.map((e) => e.source.value ~> e.target.value))(dag.edgeT)
        set foreach((n) => tmpgraph.remove(n))
        tmpgraph.nodes filter(_.inDegree == 0) foreach((n) => {
          val node = (set + n.value)
          val sink_symb = nextlevel.get(node) getOrElse
            ({id = id + 1; val s = Symbol(id.toString); nextlevel.update(node, s); s })
          dfa.add(LDiEdge(src_symb, sink_symb)(ResourceLabel(n.value.asInstanceOf[Resource]))) // TODO: Generic
        })
      }}

      if (nextlevel.size != 0) { grunt(dfa, nextlevel.toMap) }
    }

    // add start state
    val phi_symb = Symbol(id.toString)
    val dfa = MGraph.from[Symbol, LDiEdge](Seq(phi_symb), Seq.empty)

    grunt(dfa, HashMap(Set()->phi_symb))
    dfa
  }

  // Optimize
  private def Complexity[N](graph: MGraph[N, DiEdge],
                            level: Set[Set[MGraph[N, DiEdge]#NodeT]])
                            /*(implicit edgeT: TypeTag[DiEdge[N]])*/: List[Int] = {

    val nextlevel = mutable.Set.empty[Set[MGraph[N, DiEdge]#NodeT]]

    level.foreach { (set) => {
      // TODO : This is a costly operation, rewrite
      // could be that after remove we can add
      val tmpgraph = MGraph.from(graph.nodes.map(_.value),
                                 graph.edges.map((e) => e.source.value ~> e.target.value))(graph.edgeT)
      set.foreach { (n) => tmpgraph.remove(n.value) }
      val nodes0 = tmpgraph.nodes.filter(_.inDegree == 0)
      (nodes0 foreach {(n) => nextlevel.add(set + n)})
    }}

    if (nextlevel.size == 0) List(0)
    else nextlevel.size :: Complexity(graph, nextlevel.toSet /* Convert to immutable set */)
  }

  def apply(mainFile: String, modulePath: Option[String] = None) {
    runPipeline(driver.prepareContent(mainFile, modulePath))
  }

  def runPipeline(puppetProgram: String) {

    import puppet.driver.{PuppetDriver => driver}

    val im_graph = driver.compile(puppetProgram)
    driver.printDOTGraph(im_graph)

    val dfa = DAGtoDFA(im_graph)
    val dot_str = DFAtoDot(dfa)
    println(dot_str)
    val dfa_fskatlabel = labelstoFSKATExpr(dfa)
    val fskat_expr = DFAtoRegExpr(dfa_fskatlabel)
    // println(PrettyPrintFSKATExpr(fskat_expr))
    println("------------------------------------------------------------------")
    val z3 = new Z3Puppet
    val res = z3.isSatisfiable(fskat_expr)
    println(res)
    println("---------------------- XX --------------------")
  }
}
