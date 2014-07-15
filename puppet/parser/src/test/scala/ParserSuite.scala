import puppet.syntax._
import puppet.parser._
import org.scalatest.FunSuite

import java.io.File

class ParserSpec extends FunSuite {

  private def recursiveListFiles (f: File): Array[File] = {
    val these = f.listFiles
    these ++ these.filter (_.isDirectory).flatMap (recursiveListFiles)
  }

  for (f <- recursiveListFiles(new File ("./example/good/")).filter(_.isFile)) {

    test(s"$f: Parse -> Pretty -> Parse should be identity") {

      val content = scala.io.Source.fromFile (f).getLines () mkString "\n"
      val ast = PuppetParser (content)
      assert(PuppetParser (PrettyPrintAST.printAST (ast)) == ast)

    }

  }
}
