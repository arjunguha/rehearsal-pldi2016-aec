class ScalabilityTest extends org.scalatest.FunSuite {
  import rehearsal._
  import rehearsal.Implicits._
  import SymbolicEvaluator.{predEquals, exprEquals, isDeterministic, isDeterministicError}
  import PuppetSyntax._
  import java.nio.file.Paths
  import ResourceModel._
  import scalax.collection.Graph
  import scalax.collection.GraphEdge.DiEdge
  import scala.concurrent._
  import scala.concurrent.duration._
  import ExecutionContext.Implicits.global

  test("scale"){
    var ress: Map[Node, ResourceModel.Res] = Map()
    var deps: Graph[Node, DiEdge] = Graph()
    for(i <- 0.until(10)){
      val p = "/f" 
      val n = Node("file", p + i)
      ress = ress + (n -> File(Paths.get(p), CInline("content" + i), true))
      deps = deps + n
      val g = ResourceGraph(ress, deps).fsGraph("ubuntu-trusty")
      try {
        val (isDeterministic, t) =
                Await.result(Future(time(SymbolicEvaluator.isDeterministic(g))),
                             5.minutes)
        assert (isDeterministic == true)
        println(s"$i, $t, $isDeterministic, $g")
      }
      catch {
        case exn:TimeoutException => {
          println(s"$i, timedout")
        }
      }
    }
  }
}