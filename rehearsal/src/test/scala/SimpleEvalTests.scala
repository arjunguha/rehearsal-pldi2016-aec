class SimpleEvalTests extends org.scalatest.FunSuite {

  import parser.Syntax._
  import parser.Parser._
  import parser.Evaluator._
  import parser.ParseError
  import java.nio.file._
  import scala.collection.JavaConversions._

  for (path <- Files.newDirectoryStream(Paths.get("eval-tests"))) {

    test(path.toString) {
      val v = eval(expandAll(parseFile(path.toString)))
      assert(isValue(v), s"$v is not a value")
    }

  }

}