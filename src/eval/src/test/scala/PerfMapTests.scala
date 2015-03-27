import eval._

class PerfMapTests extends org.scalatest.FunSuite {

  import Implicits._
  import java.nio.file.{Path, Paths}

  type State = PerfMap[Path, FileState]

  import scala.language.implicitConversions
  implicit def toPathState(elem: (String, FileState)) =
    (Paths.get(elem._1), elem._2)

  test("Empty map should have same hash code") {
    val map1: State = PerfMap.empty 
    val map2: State = PerfMap.empty
    assert(map1.hashCode == map2.hashCode)
  }

  test("Same map should have same hash code") {
    val map1: State = PerfMap("/usr" -> IsDir)
    val map2: State = PerfMap("/usr" -> IsDir)
    assert(map1.hashCode == map2.hashCode)
  }

  test("Order of insert does not affect hash code") {
    val usr: State = PerfMap.empty + ("/usr" -> IsDir)
    val usrbin = usr + ("/bin" -> IsDir)

    val bin: State = PerfMap.empty + ("/bin" -> IsDir)
    val binusr = bin + ("/usr" -> IsDir)

    assert(usrbin.hashCode == binusr.hashCode)
  }

  test("Order of delete does not affect hash code") {
    val basemap: State = PerfMap(
      "/usr" -> IsDir,
      "/bin" -> IsDir,
      "/usr/include" -> IsDir,
      "/usr/lib" -> IsDir
    )

    val usrbininclude = basemap - "/usr/lib"
    val usrbin1 = usrbininclude - "/usr/include"

    val usrbinlib = basemap - "/usr/include"
    val usrbin2 = usrbinlib - "/usr/lib"

    assert(usrbin1.hashCode == usrbin2.hashCode)
  }

  test("delete after add does not affect hash code") {
    val basemap: State = PerfMap(
      "/usr" -> IsDir,
      "/bin" -> IsDir
    )

    val basemapAdd = basemap + ("/usr/lib" -> IsDir)
    val basemapAddDel = basemapAdd - "/usr/lib"
//     assert(basemapAddDel == basemap)
    assert(basemap.hashCode == basemapAddDel.hashCode)
  }

  test("add after delete does not affect hash code") {
    val basemap: State = PerfMap(
      "/usr" -> IsDir,
      "/bin" -> IsDir,
      "/usr/lib" -> IsDir
    )

    val basemapDel = basemap - "/usr/lib"
    val basemapDelAdd = basemapDel + ("/usr/lib" -> IsDir)

    assert(basemap.hashCode == basemapDelAdd.hashCode)
  }

  val additions = List[(Path, FileState)](
    ("/usr", IsDir),
    ("/home", IsDir),
    ("/usr/share/cowsay/cows/pony.cow", IsFile),
    ("/boot", IsDir)
  )
  
  test("order of insertion should not affect hash code") {

    val map1: State = PerfMap((additions.toSeq: _*))
    val cnt = additions.permutations.take(1000)
             .map((p) => PerfMap((p.toSeq: _*)).hashCode)
             .count(_ != map1.hashCode)
    assert(0 == cnt)
  }
}
