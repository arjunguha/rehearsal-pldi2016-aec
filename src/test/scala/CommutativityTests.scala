class CommutativityTests extends org.scalatest.FunSuite {

  import rehearsal._
  import FSSyntax._
  import Implicits._

  test("idempotent directory creation") {
    val p = ite(TestFileState("/parent", IsDir), Skip, mkdir("/parent"))
    assert(p.fileSets.reads.size == 0)
    assert(p.fileSets.writes.size == 0)
    assert(p.fileSets.dirs.size == 1)
  }

  test("Write to idempotent op path invalidates idempotent op") {
    val p = ite(TestFileState("/a", DoesNotExist), mkdir("/a"), Skip) >>
            rm("/a")
    assert(p.fileSets.dirs.size == 0)
    assert(p.fileSets.writes.size == 1)
  }

  test("non-idempotent ops should not commute") {
    val p = ite(TestFileState("/a", IsDir), Skip, mkdir("/a")) >> rm("/a")
    val q = ite(TestFileState("/a", DoesNotExist), mkdir("/a"), Skip)

    assert(false == p.commutesWith(q))
  }

  test("idempotent ops should commute") {
    val p = ite(TestFileState("/a", IsDir), Skip, mkdir("/a")) >> mkdir("/b")
    val q = mkdir("/c") >> ite(TestFileState("/a", DoesNotExist), mkdir("/a"), Skip)
    assert(p.commutesWith(q))
  }
}
