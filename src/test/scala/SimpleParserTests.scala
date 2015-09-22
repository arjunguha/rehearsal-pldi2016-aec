class SimpleParserTests extends org.scalatest.FunSuite {

  import rehearsal._
  import Parser._
  import Syntax._
  import java.nio.file._
  import scala.collection.JavaConversions._

  for (path <- Files.newDirectoryStream(Paths.get("parser-tests/good"))) {

    test(path.toString) {
      parseFile(path.toString)
    }

  }

  for (path <- Files.newDirectoryStream(Paths.get("parser-tests/bad"))) {

    test(path.toString) {
      intercept[ParseError] {
        parseFile(path.toString)
      }
    }

  }

}