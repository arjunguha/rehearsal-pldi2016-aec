package rehearsal.ppmodel

import rehearsal._

class UpdateSynth2(allPaths: List[java.nio.file.Path],
                   allContents: List[String],
                   allPackages: List[String],
                   allUsers: List[String],
                   allGroups: List[String])
  extends com.typesafe.scalalogging.LazyLogging {

  import java.nio.file.Path
  import ResourceModel._
  import fsmodel.{Expr, Seq => Sequence, Skip}
  import fsmodel.Eval._

  // Example:
  //
  // pick(Seq(a, b, c)) == Seq(a -> Seq(b, c), b -> Seq(a, c), c -> Seq(a, b))
  def pick[A](seq: Seq[A]): Seq[(A, Seq[A])] = {
    for (i <- 0.to(seq.length - 1)) yield {
      val (prefix, Seq(a, suffix @ _*)) = seq.splitAt(i)
      (a, prefix ++ suffix)
    }
  }

  val b = Seq(true, false)

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

  def distance(s1: S, s2: S): Double = (s1, s2) match {
    case (Some(st1), Some(st2)) => stateDist(st1, st2)
    case (None, None) => 0.0
    case _ => 1.0
  }

  def jointSearch(inits: Seq[S],
                  dists: Seq[Double],
                  targets: Seq[S],
                  available: Seq[Seq[Res]]): Option[List[Res]] = {
    println(s"jointSearch(dists = $dists)")
    if (dists.sum == 0) {
      Some(List())
    }
    else if (available.length == 0) {
      println("No more options")
      None
    }
    else {
      val (res, inits_, dists_, available_) = pick(available).map({ case (opts, rest) =>
        val (res, states, dists) = bestMove(inits, targets, opts)
        (res, states, dists, rest)
      })
      .minBy(_._3.sum)

      if (dists_.sum > dists.sum) {
        println("Overshot")
        None
      }
      else {
        jointSearch(inits_, dists_, targets, available_) match {
          case None => None
          case Some(lst) => Some(res :: lst)
        }
      }
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

  def guess(inputs: Seq[S], v1: List[Res], v2: List[Res]): Option[List[Res]] = {
    import fsmodel._
    val all = allResources.filterNot(_.isEmpty)
    val expr1 = Block(v1.map(_.compile): _*)
    val expr2 = Block(v2.map(_.compile): _*)
    val inits = inputs.map(st => evalErr(st, expr1))
    val targets = inputs.map(st => evalErr(st, expr2))
    val dists = inits.zip(targets).map({ case(x, y) => distance(x, y) })
    jointSearch(inits, dists, targets, all)
  }

  def delta(r1: Seq[Res], r2: Seq[Res], in: Set[State]): Seq[Res] = {
    val fs1 = r1.foldRight[Expr](Skip) { case (r, acc) => Sequence(acc, compile(r)) }
    val fs2 = r2.foldRight[Expr](Skip) { case (r, acc) => Sequence(acc, compile(r)) }
    val out1 = in.toSeq.map(eval(_, fs1))
    val out2 = in.toSeq.map(eval(_, fs2))
    val out = out1.zip(out2)

    // idea 1: (beam search?)
    // 1. generate a list of initial candidates
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

    null
  }
}
