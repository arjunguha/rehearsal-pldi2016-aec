package object rehearsal {

  import java.nio.file.{Paths, Files}
  import rehearsal.Implicits._

  type Path = java.nio.file.Path

  val root = Paths.get("/")

  def dirListing(p: Path): scala.Seq[Path] = {
    import scala.collection.JavaConversions._
    val stream = Files.newDirectoryStream(p)
    val lst = stream.toList.toSeq
    stream.close
    lst
  }

  def recursiveDirListing(p: Path): scala.Seq[Path] = {
    dirListing(p).flatMap { child =>
      if (Files.isDirectory(child)) { recursiveDirListing(child) }
      else { scala.Seq(child) }
    }
  }

  def time[A](thunk: => A): (A, Long) = {
    val start = System.currentTimeMillis
    val r = thunk
    val duration = System.currentTimeMillis - start
    r -> duration
  }

  // partition2(f, lst) = (lst1, lst2), such that f(x, y) holds for all distinct x and y in lst1.
  // Furthermore, lst1 ++ lst2 == lst without preserving ordering.
  // We assume that f is a commutative function.
  def partition2[A](f: (A, A) => Boolean, lst: List[A]): (List[A], List[A]) = {
    lst match {
      case Nil => (Nil, Nil)
      case rep :: others => {
        // Greedy: rep will be in the list
        val init = (List(rep), List[A]())
        others.foldLeft(init) {
          case ((lst1, lst2), y) => {
            if (lst1.forall(x => f(x, y))) {
              (y :: lst1, lst2)
            }
            else {
              (lst1, y :: lst2)
            }
          }
        }
      }
    }
  }

  def groupBy2[A](f: (A, A) => Boolean, lst: List[A]): List[List[A]] = partition2(f, lst) match {
    case (Nil, Nil) => Nil
    case (group, rest) => group :: groupBy2(f, rest)
  }


}
