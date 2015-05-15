import rehearsal.fsmodel._
import Implicits._

class CommutativityTests extends org.scalatest.FunSuite {

  test("idempotent directory creation") {
    val p = If(TestFileState("/parent", IsDir), Skip, Mkdir("/parent"))
    assert(p.readSet.size == 0)
    assert(p.writeSet.size == 0)
    assert(p.idemSet.size == 1)
  }

  test("Write to idempotent op path invalidates idempotent op") {
    val p = If(TestFileState("/a", DoesNotExist), Mkdir("/a"), Skip) >>
            Rm("/a")
    assert(p.idemSet.size == 0)
    assert(p.writeSet.size == 1)
  }

  /*
  test("read(a) * idempotent_mkdir(a) is not idempotent") {
    val p = If(TestFileState("/a", IsDir) && !TestFileState("/a/b", DoesNotExist),
               Mkdir("/a/b"), Skip)
    val q = If(TestFileState("/a", DoesNotExist), Mkdir("/a"), Skip)
    val expr = p * q
    assert(expr.idemSet.size == 0)
    assert(expr.writeSet.contains("/a"))
    assert(expr.readSet.contains("/a"))
  }
  */

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
