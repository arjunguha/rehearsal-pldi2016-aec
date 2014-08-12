import puppet.driver._
import org.scalatest.FunSuite
import java.io.File

class CompilerSuite extends FunSuite {

  val src = "./example/compiler/"

  private def recursiveListFiles (f: File): Array[File] = {
    val these = f.listFiles
    these ++ these.filter (_.isDirectory).flatMap (recursiveListFiles)
  }

  for (f <- recursiveListFiles (new File (src)).filter(_.isFile)) {

    test(s"compiling $f") {
      val content = scala.io.Source.fromFile (f).getLines () mkString "\n"
      PuppetDriver.printDOTGraph(PuppetDriver.compile (content))
    }

  }

}
