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

  val allResources: Seq[Res] =
    allPaths.flatMap { p =>
      allContents.flatMap { c =>
        Seq(EnsureFile(p, c)) ++
        b.map { f => File(p, c, f) }
      } ++
      b.map { f => AbsentPath(p, f) } ++
      Seq(Directory(p))
    } ++
    allPackages.flatMap { pkg => b.map { b => Package(pkg, b) } } ++
    allGroups.flatMap { g => b.map { b => Group(g, b) } } ++
    allUsers.flatMap { u =>  b.flatMap { p => b.map { h => User(u, p, h) } } }

  def dist(st1: State, st2: State): Double = {
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
