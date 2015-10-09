class SimpleEvalTests extends org.scalatest.FunSuite {

	import rehearsal._
	import PuppetParser2._
	import PuppetSyntax2._
	import PuppetEval2._
	import java.nio.file._
	import scala.collection.JavaConversions._
  import scalax.collection.Graph
  import scalax.collection.Graph._
  import scalax.collection.GraphPredef._
  import scalax.collection.GraphEdge._
  import scalax.collection.edge.Implicits._

	for (path <- Files.newDirectoryStream(Paths.get("parser-tests/good"))) {

		test(path.toString) {
			parseFile(path.toString)
			val EvaluatedManifest(resources, deps) = eval(parseFile(path.toString))
			if (deps.nodes.length == 0) {
				info("No resources found -- a trivial test")
			}
			for (node <- deps.nodes) {
				assert(primTypes.contains(node.value.typ), s"${node.value.typ} not elaborated")
			}
		}

	}

	test("simple before relationship") {

		val EvaluatedManifest(r, g) = eval(parse("""
      file{"A":
        before => File["B"]
      }
      file{"B": }
    """))

    assert(r.size == 2)
    assert(g == Graph(Node("file", "A") ~> Node("file", "B")))

	}

	test("require relationship with an array") {

		val EvaluatedManifest(r, g) = eval(parse("""
      file{"A":
        require => [File["B"], File["C"]]
      }
      file{"B": }
      file{"C": }
    """))

    assert(r.size == 3)
    assert(g == Graph(Node("file", "B") ~> Node("file", "A"),
                      Node("file", "C") ~> Node("file", "A")))
	}

}