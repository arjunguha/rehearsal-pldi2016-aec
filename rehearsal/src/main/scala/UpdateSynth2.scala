package rehearsal

object UpdateSynth extends com.typesafe.scalalogging.LazyLogging {

  import java.nio.file.{Files, Paths, Path}
  import ResourceModel._
  import FSSyntax.{Expr, Skip, Block}
  import Eval._


  // Calculates the "distance" between two states. The distance is in the range [0.0, 1.0], where 0.0 means
  // identical and 1.0 means "very different.
  //
  // TODO(arjun): A potential problem with this metric is that it doesn't rely on the total number of possible
  // paths. States don't explicitly represent paths that don't exist, so this can cause problems. We should
  // probably change it so that 1.0 means "all paths are different".
  def distance(s1: S, s2: S): Double = {

    def stateDist(st1: State, st2: State): Double = {
      var dist = 0
      val paths: Seq[Path] = (st1.keys.toSet union st2.keys.toSet).toSeq

      val vec: Seq[Double] = paths.map(p => (st1.get(p), st2.get(p)) match {
        case (None, None) => 0.0
        case (Some(_), None) => 1.0
        case (None, Some(_)) => 1.0
        case (Some(FDir), Some(FDir)) => 0.0
        case (Some(FFile(h1)), Some(FFile(h2))) => if (h1.toSeq == h2.toSeq) {
          0.0
        } else {
          1.0
        }
        case (Some(_), Some(_)) => 1.0
      })

      Math.pow(vec.sum, 1.0 / vec.length.toDouble)
    }

    (s1, s2) match {
      case (Some(st1), Some(st2)) => stateDist(st1, st2)
      case (None, None) => 0.0
      case _ => 1.0
    }
  }

  case class DomainBounds(allPaths: List[Path], allContents: List[String], allPackages: List[String],
    allUsers: List[String],  allGroups: List[String]) {

    // For testing
    def withPaths(paths: Path*): DomainBounds = this.copy(allPaths = paths.toList)
    def withContents(contents: String*): DomainBounds = this.copy(allContents = contents.toList)

    private val b = Seq(true, false)

    // When flattened, this is a list of all resources. But, we represent the
    // resources as nested sequences:
    //
    // Seq(Seq(a1, a2), Seq(b1, b2), ...)
    //
    // Where resources in a nested group are mutually exclusive.
    // For example:
    //
    // Seq(Seq(Package("vim", present = true), Package("vim", present = false)),
    //     Seq(Package("emacs", present = true), Package("emacs", present = false)),
    //     ..)
    val allResources: Seq[Seq[Res]] =
      allPaths.map { p =>
        allContents.flatMap { c =>
          Seq(EnsureFile(p, c)) ++
            b.map { f => File(p, c, f) }
        } ++
          b.map { f => AbsentPath(p, f) } ++
          Seq(Directory(p))
      } ++
        allPackages.map { pkg => b.map { b => Package(pkg, b) } } ++
        allGroups.map { g => b.map { b => Group(g, b) } } ++
        allUsers.map { u =>  b.flatMap { p => b.map { h => User(u, p, h) } } }

  }

  object DomainBounds {
    val empty = DomainBounds(List(), List(), List(), List(), List())
  }

  trait Synthesizer {

    def synthesize(inits: Seq[S], dists: Seq[Double], targets: Seq[S], available: Seq[Seq[Res]]): Option[List[Res]]

  }

  trait GreedySynthesizer extends Synthesizer {

    // Example:
    //
    // pick(Seq(a, b, c)) == Seq(a -> Seq(b, c), b -> Seq(a, c), c -> Seq(a, b))
    def pick[A](seq: Seq[A]): Seq[(A, Seq[A])] = {
      for (i <- 0.to(seq.length - 1)) yield {
        val (prefix, Seq(a, suffix @ _*)) = seq.splitAt(i)
        (a, prefix ++ suffix)
      }
    }

    // Finds the best resource in options to apply to bring all states in
    // inits closer to target. Returns the resource and the sequence of states
    // that are produced by apply the resource to each state in inits.
    def bestMove(inits: Seq[S],
                 targets: Seq[S],
                 options: Seq[Res]):(Res, Seq[S], Seq[Double]) = {
      options.map({ res =>
        val inits_ = inits.map(st => evalErr(st, res.compile))
        val dists = inits_.zip(targets).map({ case (x, y) => distance(x, y) })
        (res, inits_, dists)
      })
        .minBy({ case (_, _, dists) => dists.sum })
    }


    def synthesize(inits: Seq[S], dists: Seq[Double], targets: Seq[S], available: Seq[Seq[Res]]): Option[List[Res]] = {
      logger.info(s"jointSearch(dists = $dists)")
      if (dists.sum == 0) {
        Some(List())
      }
      else if (available.length == 0) {
        logger.info("No more options")
        None
      }
      else {
        val (res, inits_, dists_, available_) = pick(available).map({ case (opts, rest) =>
          val (res, states, dists) = bestMove(inits, targets, opts)
          (res, states, dists, rest)
        })
          .minBy(_._3.sum)

        if (dists_.sum > dists.sum) {
          logger.info("overshot")
          None
        }
        else {
          synthesize(inits_, dists_, targets, available_) match {
            case None => None
            case Some(lst) => Some(res :: lst)
          }
        }
      }
    }

  }

  trait SynthesizeVerify extends Synthesizer {
    val bounds: DomainBounds
    import bounds._

    def evalErrRes(st: S, lst: List[Res]) = {
      evalErr(st, Block(lst.map(_.compile): _*))
    }

    def guess(inputs: Seq[S], v1: List[Res], v2: List[Res]): Option[List[Res]] = {
      val all = allResources.filterNot(_.isEmpty)
      val expr1 = Block(v1.map(_.compile): _*)
      val expr2 = Block(v2.map(_.compile): _*) // TODO(arjun): needless work
      val inits = inputs.map(st => evalErr(st, expr1))
      val targets = inputs.map(st => evalErr(st, expr2))
      val dists = inits.zip(targets).map({ case(x, y) => distance(x, y) })
      synthesize(inits, dists, targets, all)
    }

    def synth(precond: Set[State], inputs: Seq[S], v1: List[Res], v2: List[Res]): Option[(Set[State], List[Res])] = {
      guess(inputs, v1, v2) match {
        // We have failed... use the latest counter example as a precondition
        // and start over
        case None => {
          val cex = inputs.head.get
          logger.info(s"Could not guess next, adding precondition: $cex")
          if(precond.contains(cex))
            throw Unexpected("Generated duplicate precondition")
          synth(precond + inputs.head.get, Seq(inputs.last), v1, v2)
        }
        case Some(delta) => {
          logger.info(s"Synthesized delta: $delta")
          val e1 = Block(v1.map(_.compile): _*)
          val eDelta = Block((delta).map(_.compile): _*)
          val e2 = Block(v2.map(_.compile): _*) // TODO(arjun): needless work
          SymbolicEvaluator2.exprEqualsSynth(precond, e1, eDelta, e2) match {
            case None => Some(precond, delta)
            case Some(cex) => {
              logger.info(s"Counterexample input state: $cex")
              logger.info(s"Running v1 on cex: ${evalErrRes(cex, v1)}")
              logger.info(s"Running v1 + delta on cex: ${evalErrRes(cex, v1 ++ delta)}")
              logger.info(s"Running v2 on cex: ${evalErrRes(cex, v2)}")
              synth(precond, cex +: inputs, v1, v2)
            }
          }
       } 
      }
    }


    // idea 1: (beam search?)
    // 1. egnerate a list of initial candidates
    // 2. evaluate each candidate on states from out LHS
    // 3. take distance from new state to RHS
    // 4. repeat process using top N candidates
    // 5. each time, expand list by making a copy of each top candidate with each resource appended
    // 6. stop when distance of 0 is found
    // We could return here, or we could continue:
    // 7. minimize the candidate by attempting to remove each element and checking if dist = 0

    // idea 2: (a genetic algorithm)
    // 1. generate a list of initial candidates
    // 2. evaluate each candidate on states from out LHS
    // 3. take distance from new state to RHS
    // 4. repeat process using best candidate
    // 5. each time, produce a large list by randomly mutating copies of best candidate
    // 6. stop when distance of 0 is found
    // We could return here, or we could continue:
    // 7. minimize the candidate by attempting to remove each element and checking if dist = 0
  }

  class UpdateSynth2(val bounds: DomainBounds) extends SynthesizeVerify with GreedySynthesizer

  def allPaths(r: Res): Set[Path] = r match {
    case File(p, _, _) => Set(p)
    case EnsureFile(p, _) => Set(p)
    case AbsentPath(p, _) => Set(p)
    case Directory(p) => Set(p)
    case Package(_, _) => Set()
    case Group(_, _) => Set()
    case User(_, _, _) => Set()
  }

  def allContents(r: Res): Set[String] = r match {
    case File(_, c, _) => Set(c)
    case EnsureFile(_, c) => Set(c)
    case AbsentPath(_, _) => Set()
    case Directory(_) => Set()
    case Package(_, _) => Set()
    case Group(_, _) => Set()
    case User(_, _, _) => Set()
  }

  def allPackages(r: Res): Set[String] = r match {
    case File(_, _, _) => Set()
    case EnsureFile(_, _) => Set()
    case AbsentPath(_, _) => Set()
    case Directory(_) => Set()
    case Package(p, _) => Set(p)
    case Group(_, _) => Set()
    case User(_, _, _) => Set()
  }

  def allUsers(r: Res): Set[String] = r match {
    case File(_, _, _) => Set()
    case EnsureFile(_, _) => Set()
    case AbsentPath(_, _) => Set()
    case Directory(_) => Set()
    case Package(_, _) => Set()
    case Group(_, _) => Set()
    case User(u, _, _) => Set(u)
  }

  def allGroups(r: Res): Set[String] = r match {
    case File(_, _, _) => Set()
    case EnsureFile(_, _) => Set()
    case AbsentPath(_, _) => Set()
    case Directory(_) => Set()
    case Package(_, _) => Set()
    case Group(g, _) => Set(g)
    case User(_, _, _) => Set()
  }

  val initState = Some(Map(Paths.get("/") -> Eval.FDir))

  def calculate(manifest1: String, manifest2: String): Unit = {
    val graph1 = puppet.syntax.parse(manifest1).desugar().toGraph(Map()).head._2
    val graph2 = puppet.syntax.parse(manifest2).desugar().toGraph(Map()).head._2

    assert(SymbolicEvaluator2.isDeterministic(toFileScriptGraph(graph1)),
           "V1 is not deterministic")
    assert(SymbolicEvaluator2.isDeterministic(toFileScriptGraph(graph2)),
           "V2 is not deterministic")

    val v1 = topologicalSort(graph1).map(r => ResourceToExpr.convert(r))
    val v2 = topologicalSort(graph2).map(r => ResourceToExpr.convert(r))

    val all = v1 ++ v2

    logger.info(s"V1: $v1")
    logger.info(s"V2: $v2")

    val bounds = DomainBounds(unions(all.map(allPaths)).toList,
      unions(all.map(allContents)).toList,
      unions(all.map(allPackages)).toList,
      unions(all.map(allUsers)).toList,
      unions(all.map(allGroups)).toList)

    val upd = new UpdateSynth2(bounds)

    val r = upd.synth(Set(), Seq(initState), v1, v2)
    logger.info(s"Synthesis result: $r")
    println(r)
  }

  def calculate(manifest1: Path, manifest2: Path): Unit = {
    calculate(new String(Files.readAllBytes(manifest1)),
              new String(Files.readAllBytes(manifest2)))
  }

}
