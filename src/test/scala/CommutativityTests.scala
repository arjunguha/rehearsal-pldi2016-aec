class CommutativityTests extends org.scalatest.FunSuite {

  import rehearsal._
  import FSSyntax._
  import Implicits._

  test("idempotent directory creation") {
    val p = If(TestFileState("/parent", IsDir), Skip, Mkdir("/parent"))
    assert(p.fileSets.reads.size == 0)
    assert(p.fileSets.writes.size == 0)
    assert(p.fileSets.dirs.size == 1)
  }

  test("Write to idempotent op path invalidates idempotent op") {
    val p = If(TestFileState("/a", DoesNotExist), Mkdir("/a"), Skip) >>
            Rm("/a")
    assert(p.fileSets.dirs.size == 0)
    assert(p.fileSets.writes.size == 1)
  }

  test("non-idempotent ops should not commute") {
    val p = If(TestFileState("/a", IsDir), Skip, Mkdir("/a")) >> Rm("/a")
    val q = If(TestFileState("/a", DoesNotExist), Mkdir("/a"), Skip)

    assert(false == p.commutesWith(q))
  }

  test("idempotent ops should commute") {
    val p = If(TestFileState("/a", IsDir), Skip, Mkdir("/a")) >> Mkdir("/b")
    val q = Mkdir("/c") >> If(TestFileState("/a", DoesNotExist), Mkdir("/a"), Skip)
    assert(p.commutesWith(q))
  }
}
