package test.puppet

import puppet.driver._
import org.scalatest._
import org.scalatest.prop._

import java.io.File

class CompilerSpec extends PropSpec with PropertyChecks with Matchers {

  // val src = "./example/compiler"
  val src = "./example"

  private def recursiveListFiles (f: File): Array[File] = {
    val these = f.listFiles
    these ++ these.filter (_.isDirectory).flatMap (recursiveListFiles)
  }

  property ("Compiler should not throw exceptions") {

    val files = Table ("file", recursiveListFiles (new File (src)).filter (_.isFile).toSeq:_*)

    forAll (files) {(f: File) => {
      val content = scala.io.Source.fromFile (f).getLines () mkString "\n"
      PuppetDriver (content)
    }}
  }
}
