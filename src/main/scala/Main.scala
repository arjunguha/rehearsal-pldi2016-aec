package rehearsal

package repl {

  import java.nio.file.Paths
  import UpdateSynth._

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
      case List("update", manifest1, manifest2) => {
        UpdateSynth.calculate(Paths.get(manifest1), Paths.get(manifest2))
      }
      case List("synthbench", n, trial) => {
        println("Delta, Type, Time")
        0.until(trial.toInt) foreach { _ =>
          0.to(n.toInt) foreach { n =>
            val lst = fileResources.take(n).toList

            val (_, t1) = time(execLists(List(), lst))
            println(s"$n, Add,$t1")
            val (_, t2) = time(execLists(lst, List()))
            println(s"$n, Remove, $t2")
            val x = n / 2
            val (_, t3) = time(execLists(lst.take(x), lst.drop(x)))
            println(s"$n, Add/Remove, $t3")
          }
        }
      }
      case List("synthprefixbench", trial) => {
        println("Delta, Prefix, Time")
        0.until(trial.toInt).foreach { _ =>
          List(10, 20, 30, 40).foreach { prefixLen =>
           List(1, 2, 3, 4, 5).foreach { deltaLen =>
             val lst1 = fileResources.take(prefixLen).toList
             val lst2 = fileResources.take(prefixLen + deltaLen).toList
             val (_, t) = time(execLists(lst1, lst2))
             println(s"$deltaLen, $prefixLen, $t")
           }
          }
        }
      }
      case List("benchmark", "prefix", n, trial) => { // approx. 50
        // Synthesize the delta between two distinct manifests of size 3 with a common prefix of size n.
        println("count,time")
        0.until(Integer.parseInt(trial)).map(_ => {
          0.to(Integer.parseInt(n)).map(x => {
            val pre = genPrefix(x)
            val start = java.lang.System.currentTimeMillis()
            uncurry(execLists)(gen(3) match {
              case (a, b) =>  (pre ++ a, pre ++ b)
            })
            val end = java.lang.System.currentTimeMillis()
            println(s"$x,${end - start}")
          })
        })
      }
      case List("benchmark", "second", n, trial) => { // approx. 10
        // Grow a manifest of size n and synthesize a delta from an empty manifest.
        println("count,time")
        0.until(trial.toInt) foreach { _ =>
          0.to(n.toInt) foreach { n =>
            val lst2 = fileResources.take(n).toList
            val (_, t) = time(execLists(List(), lst2))
            println(s"$n, both,$t")
          }
        }
      }
      case List("benchmark", "first", n, trial) => { // approx. 5
        // Grow a manifest of size n and synthesize a delta to an empty manifest.
        println("count,time")
        val x = 23
        0.until(trial.toInt) foreach { _ =>
          0.to(n.toInt) foreach { n =>
            val lst1 = fileResources.take(n).toList
            val (_, t) = time(execLists(lst1, List()))
            println(s"$n,first,$t")
          }
        }
      }
      case List("benchmark", "both", n, trial) => { // approx. 5
        // Grow two distinct manifests of the same size and find a delta.
        println("count,time")
        0.until(trial.toInt) foreach { _ =>
          0.to(n.toInt) foreach { n =>
            val lst1 = fileResources.take(n).toList
            val lst2 = fileResources.drop(n).take(n).toList
            val (_, t) = time(execLists(lst1, lst2))
            println(s"$n,both,$t")
          }
        }
      }
      case List("parseall", path) => runOnAll(path, "parser", "parsed") {
        PuppetParser.parseFile(_)
      }
      case List("evalall", path) => runOnAll(path, "evaluator", "evaluated") {
        PuppetParser.parseFile(_).eval
      }
      case List("detersuite") => DeterminismBenchmarks.run()
      case List("detersizes") => DeterminismSizeTables.run()
      case List("deterstress") => DeterStressBenchmark.run()
      case args => {
        sys.error(s"Invalid command-line arguments: $args")
      }
    }

  }

}
