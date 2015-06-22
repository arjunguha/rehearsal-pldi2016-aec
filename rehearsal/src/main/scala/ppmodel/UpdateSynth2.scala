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

<<<<<<< HEAD
  def distance(s1: Option[State], s2: Option[State]): Double = (s1, s2) match {
    case (Some(st1), Some(st2)) => stateDist(st1, st2)
    case (None, None) => 0.0
    case _ => 1.0
  }

  def stateDist(st1: State, st2: State): Double = {
    var dist = 0
=======
  def dist(st1: State, st2: State): Double = {
>>>>>>> 997e939f838cdee747eaae26340ae34eb27f674a
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

<<<<<<< HEAD
  def nextMove(stInit: State, stFinal: Option[State],
               options: Seq[Res]): (Res, Option[State], Double) = {
    assert(!options.isEmpty)

    options.map({ res =>
      val st = eval(stInit, res.compile)
      (res, st, distance(st, stFinal))
    })
    .minBy(_._3)
  }

  // Example:
  //
  // pick(Seq(a, b, c)) == Seq(a -> Seq(b, c), b -> Seq(a, c), c -> Seq(a, b))
  def pick[A](seq: Seq[A]): Seq[(A, Seq[A])] = {
    for (i <- 0.to(seq.length - 1)) yield {
      val (prefix, Seq(a, suffix @ _*)) = seq.splitAt(i)
      (a, prefix ++ suffix)
    }
  }

  def greedySearch(dist: Double, stInit: State, stFinal: Option[State],
                   available: Seq[Seq[Res]]): Option[List[Res]] = {
    if (dist == 0) {
      Some(List())
    }
    else if (available.length == 0) {
      println("No more options")
      None
    }
    else {
      val ((nextRes, nextSt, nextDist), rest) = pick(available)
        .map({ case (options, others) => {
          (nextMove(stInit, stFinal, options), others)
         } })
        .minBy(_._1._3)
      if (nextDist > dist) {
        None // greedy: don't move further away
      }
      else if (nextDist == dist) {
        Some(List(nextRes))
      }
      else {
        nextSt match {
          case None => {
            if (stFinal == None) {
              Some(List(nextRes))
            }
            else {
              None
            }
          }
          case Some(stInit_) => {
            greedySearch(nextDist, stInit_, stFinal, rest) match {
              case None => None
              case Some(seq) => Some(nextRes :: seq)
            }
          }
        }
      }
    }
  }

  def guess(stInit: State, res1: List[Res], res2: List[Res]): Option[List[Res]] = {
    import fsmodel._
    val all = allResources.filterNot(_.isEmpty)
    val st1 = eval(stInit, Block(res1.map(_.compile): _*))
    val st2 = eval(stInit, Block(res2.map(_.compile): _*))
    (st1, st2) match {
      case (None, None) => Some(List())
      case (None, Some(_)) => None
      case (Some(st1_), _) => {
        greedySearch(distance(st1, st2), st1_, st2,
                     all)
      }
    }
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
