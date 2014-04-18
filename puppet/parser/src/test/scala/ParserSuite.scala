import org.scalatest.PropSpec
import org.scalatest.prop._
import org.scalatest.matchers.ShouldMatchers
import puppet._

import java.io.File

class ParserSpec extends PropSpec with PropertyChecks with ShouldMatchers {

/*
  test("basic test") {
    assert(PuppetParser("$a = / 4").successful == false)
  }
*/

  private def recursiveListFiles (f: File): Array[File] = {
    val these = f.listFiles
    these ++ these.filter (_.isDirectory).flatMap (recursiveListFiles)
  }

  property ("Parse -> Pretty -> Parse should be identity") {

  val files = Table ("file", recursiveListFiles (new File ("./example/")).filter (_.isFile).toSeq: _*)

  forAll (files) {(f: File) => {
    val content = scala.io.Source.fromFile (f).getLines () mkString "\n"
    val ast = PuppetParser (content)
    PuppetParser (PrettyPrintAST.printAST (ast)) should equal (ast)
  }}}
}
