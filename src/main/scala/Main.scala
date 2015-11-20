package rehearsal

package repl {

  import java.nio.file.Paths

  private object Main extends App {
    def runOnAll[A](path: String, noun: String, pastVerb: String)(action: String => A) {
      import java.io.File
      import scala.util.{Try, Success, Failure}
      def walkTree(file: File): Iterable[File] = {
        val children = new Iterable[File] {
          def iterator = if (file.isDirectory) file.listFiles.iterator else Iterator.empty
        }
        Seq(file) ++: children.flatMap(walkTree(_))
      }
      var count = 0
      var total = 0
      println(s"Running $noun on all Puppet files within $path.")
      walkTree(new File(path)).filter(_.getPath().endsWith(".pp")) foreach { file =>
        total += 1
        if (Try(action(file.getPath())).isSuccess) {
          println(s"Successfully $pastVerb ${file.getPath()}.")
          count += 1
        }
      }
      println(s"${pastVerb.capitalize} $count files out of $total. (${(count * 100) / total}%)")
    }

    def uncurry[A, B, C](f: (A, B) => C)(t: (A, B)): C = f(t._1, t._2)
    args.toList match {

      case List("parseall", path) => runOnAll(path, "parser", "parsed") {
        PuppetParser.parseFile(_)
      }
      case List("evalall", path) => runOnAll(path, "evaluator", "evaluated") {
        PuppetParser.parseFile(_).eval
      }
      case List("detersuite") => DeterminismBenchmarks.run()
      case List("detersizes") => DeterminismSizeTables.run()
      case List("deterstress") => DeterStressBenchmark.run()
      case List("deterbench", label, filename, os, pruning) => {
        DeterminismBenchmarks.single(label, filename, os, pruning match {
          case "prune" => true
          case "noprune" => false
        })
      }
      case args => {
        sys.error(s"Invalid command-line arguments: $args")
      }
    }

  }

}
