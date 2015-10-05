class GithubSuite extends org.scalatest.FunSuite {

  import puppet.Modules
  import puppet.graph.Resource
  import rehearsal._
  import puppet.syntax.{TopLevel, parse}
  import scala.util.{Try, Success, Failure}
  import java.nio.file.{Files, Paths, Path}
  import java.nio.charset.StandardCharsets.UTF_8
  import scala.collection.JavaConversions._
  import Evaluator._

  val env = puppet.Facter.fromFile("src/test/arjun-vm.facter") getOrElse
    (throw new Exception("Facter environment not found"))

  val repos = Files.readAllLines(Paths.get("src/test/github.txt"), UTF_8)

  for (repo <- repos) {
    test(repo) {
      // val topLevel = findPuppetFiles(Paths.get(repo)).get
      // val g = GuessClasses.guessLoad(topLevel).desugar.toGraph(env).head._2
      val g = toGraph(eval(expandAll(Parser.parseFile(repo))))
      val files = g.nodes.filter(_.typ == "File")
      val numEdges = g.edges.size
      val numFiles = files.size
      val fileDeps = files.map(_.inDegree).sum
      val numNodes = g.nodes.size
      println(s"$repo, $numFiles, $fileDeps, $numNodes, $numEdges")
      val rg = toFileScriptGraph(g)
      println("Slicing...")
      val g_ = Slicing.sliceGraph(rg)
      println("Checking...")
      val det = SymbolicEvaluator.isDeterministic(g_)
      println(s"isDeterministic: $det")
    }
  }

}
