class SimpleEvalTests extends org.scalatest.FunSuite {

	import rehearsal._
	import PuppetParser2._
	import Syntax._
	import PuppetEval2._
	import java.nio.file._
	import scala.collection.JavaConversions._

	for (path <- Files.newDirectoryStream(Paths.get("parser-tests/good"))) {

		test(path.toString) {
			parseFile(path.toString)
			val (resources, deps) = eval(parseFile(path.toString))
			if (deps.nodes.length == 0) {
				info("No resources found -- a trivial test")
			}
			for (node <- deps.nodes) {
				assert(primTypes.contains(node.value.typ), s"${node.value.typ} not elaborated")
			}
		}

	}

}