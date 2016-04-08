package rehearsal

object Main extends App {

  import scala.concurrent._
  import scala.concurrent.duration._
  import ExecutionContext.Implicits.global
  import java.nio.file.Files
  import Implicits._
  import scala.util.{Try, Success, Failure}

  sealed trait Command
  case object Checker extends Command
  case object DeterminismBenchmark extends Command
  case object PruningSizeBenchmark extends Command
  case object IdempotenceBenchmark extends Command
  case object ScalabilityBenchmark extends Command

  case class Config(
    command: Option[Command],
    filename: Option[Path],
    os: Option[String],
    label: Option[String],
    pruning: Option[Boolean],
    deterministic: Option[Boolean],
    idempotent: Option[Boolean],
    size: Option[Int])

  val parser = new scopt.OptionParser[Config]("rehearsal") {

    def filename() = {
      opt[String]("filename").required
        .action((x, c)  => c.copy(filename = Some(x.toPath)))
    }

    def label() = {
      opt[String]("label").required
        .action((x, c) => c.copy(label = Some(x)))
    }

    def os() = {
      opt[String]("os").required
        .action((x, c) => c.copy(os = Some(x)))
    }

    def size() = {
      opt[Int]("size").required.action((x, c) => c.copy(size = Some(x)))
    }

    head("rehearsal", "0.1")

    cmd("check")
        .action((_, c) => c.copy(command = Some(Checker)))
        .text("Check a Puppet manifest for errors.")
        .children(filename, os)

    cmd("benchmark-pruning-size")
      .action((_, c) => c.copy(command = Some(PruningSizeBenchmark)))
      .text("Benchmark the effect of pruning on the number of writable paths")
      .children(filename, label, os)

    cmd("benchmark-idempotence")
      .action((_, c) => c.copy(command = Some(IdempotenceBenchmark)))
      .text("Benchmark the performance of idempotence-checking")
      .children(filename, label, os,
        opt[Boolean]("idempotent").required
          .action((x,c) => c.copy(idempotent = Some(x))))

    cmd("benchmark-determinism") action { (_, c) =>
      c.copy(command = Some(DeterminismBenchmark))
    } text("Benchmark determinism checking") children(
      filename,
      label,
      os,
      opt[Boolean]("pruning").required
        .action((x, c) => c.copy(pruning = Some(x))),
      opt[Boolean]("deterministic").required
          .action((x, c) => c.copy(deterministic = Some(x)))
    )

    cmd("scalability-benchmark")
      .action((_, c) => c.copy(command = Some(ScalabilityBenchmark)))
      .text("Benchmark determinism-checking scaling")
     .children(size)

  }

  def checker(filename: String, os: String): Unit = {
    if (!Set("ubuntu-trusty", "centos-6").contains(os)) {
      println("""Error: supported operating systems are 'ubuntu-trusty' and 'centos-6'""")
      return
    }

    if (!Files.isRegularFile(filename) || !Files.isReadable(filename)) {
      println("Error: not a readable file: $filename")
      return
    }

    Try(PuppetParser.parseFile(filename.toString)
          .eval.resourceGraph.fsGraph(os)
          .addRoot(FSGraph.key())
          .contractEdges()) match {
      case Success(g) => {
        print("Checking if manifest is deterministic ... ")
        if (SymbolicEvaluator.isDeterministic(g.pruneWrites)) {
          println("OK.")
        }
        else {
          println("FAILED.")
          return
        }

        print("Checking if manifest is idempotent ... ")
        if (g.expr.pruneIdem.isIdempotent) {
          println("OK.")
        }
        else {
          println("FAILED.")
          return
        }
      }
      case Failure(ParseError(msg)) => {
        println("Error parsing file.")
        println(msg)
      }
      case Failure(EvalError(msg)) => {
        println("Error evaluating file.")
        println(msg)
      }
      case Failure(PackageNotFound(distro, pkg)) => {
        println(s"Package not found: $pkg.")
      }
      case Failure(exn) => throw exn
    }
  }

  parser.parse(args, Config(None, None, None, None, None, None, None, None)) match {
    case None => {
      println(parser.usage)
      System.exit(1)
    }
    case Some(config) => {
      config.command match {
        case None => {
          println(parser.usage)
          System.exit(1)
        }
        case Some(Checker) => {
          val filename = config.filename.get
          val os = config.os.get
          checker(filename.toString, os)
        }
        case Some(IdempotenceBenchmark) => {
          val filename = config.filename.get
          val label = config.label.get
          val os = config.os.get
          val expected = config.idempotent.get
          val g = PuppetParser.parseFile(filename.toString).eval.resourceGraph
            .fsGraph(os)
            .expr
            .pruneIdem
          val (isIdempotent, t) = time(g.isIdempotent)
          assert (expected == isIdempotent)
          println(s"$label, $t")
        }
        case Some(PruningSizeBenchmark) => {
          val filename = config.filename.get
          val label = config.label.get
          val os = config.os.get
          val g1 = PuppetParser.parseFile(filename.toString)
            .eval.resourceGraph.fsGraph(os)
            .addRoot(FSGraph.key())
            .contractEdges()
          val g2 = g1.pruneWrites()
          val paths = g1.expr.fileSets.writes.size
          val postPruningPaths =  g2.pruneWrites.expr.fileSets.writes.size
          println(s"$label, $paths, $postPruningPaths")
        }
        case Some(DeterminismBenchmark) => {

          val label = config.label.get
          val pruningStr = if (config.pruning.get) "pruning" else "no-pruning"
          val shouldBeDeterministic = config.deterministic.get

          val g_ = PuppetParser.parseFile(config.filename.get.toString)
            .eval.resourceGraph.fsGraph(config.os.get)
            .addRoot(FSGraph.key())
            .contractEdges()

          val g = if (config.pruning.get) g_.pruneWrites() else g_
          try {
            val (isDeterministic, t) =
              Await.result(Future(time(SymbolicEvaluator.isDeterministic(g))),
                           5.minutes)
              assert (shouldBeDeterministic == isDeterministic)
              println(s"$label, $pruningStr, $t")
          }
          catch {
            case exn:TimeoutException => {
              println(s"$label, $pruningStr, timedout")
            }
          }
        }
        case Some(ScalabilityBenchmark) => {
          val n = config.size.get
          import ResourceModel.{File, CInline}
          import scalax.collection.Graph
          import scalax.collection.GraphEdge.DiEdge
          val e = ResourceModel.File(path = "/a".toPath, content = CInline("content"), force = false)
            .compile("ubuntu-trusty")
          val nodes = 0.until(n).map(n => FSGraph.key())
          val graph = FSGraph(nodes.map(n => n -> e).toMap, Graph(nodes: _*))
          val (_, t) = time(SymbolicEvaluator.isDeterministic(graph.contractEdges.pruneWrites))
          println(s"$n, $t")
        }
      }
    }
  }

}
