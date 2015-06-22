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
}
