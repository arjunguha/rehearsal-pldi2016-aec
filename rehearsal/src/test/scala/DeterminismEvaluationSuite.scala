class DeterminismEvaluationSuite extends org.scalatest.FunSuite {

  import rehearsal._
  import java.nio.file._


  test("vagrant-cakephp") {
    val g = findPuppetFiles(Paths.get("benchmarks/puppet-mosh")).get.desugar.toGraph(Map())
    println(g)


    //ast.desugar.toGraph(Map())
  }

}