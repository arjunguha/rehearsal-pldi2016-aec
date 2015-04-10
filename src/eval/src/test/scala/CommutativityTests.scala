import eval._
import eval.Implicits._
import Ample._

class CommutativityTests extends org.scalatest.FunSuite {

  test("idempotent directory creation") {
    val p = If(TestFileState("/parent", IsDir), Skip, Mkdir("/parent"))
    assert(p.readSet.size == 0)
    assert(p.writeSet.size == 0)
    assert(p.idemSet.size == 1)
  }

  test("non-idempotent unatomic ops should not commute") {
    val p = If(TestFileState("/a", IsDir), Skip, Mkdir("/a")) >>
            Rm("/a")
    val q = If(TestFileState("/a", DoesNotExist), Mkdir("/a"), Skip)

    assert(false == p.commutesWith(q))
  }

  test("non-idempotent atomic ops should not commute") {
    val p = Atomic(If(TestFileState("/a", IsDir), Skip, Mkdir("/a")) >>
                   Rm("/a"))
    val q = Atomic(If(TestFileState("/a", DoesNotExist), Mkdir("/a"), Skip))

    assert(false == p.commutesWith(q))
  }

  test("Atomic idempotent ops should commute") {
    val p = Atomic(If(TestFileState("/a", IsDir), Skip, Mkdir("/a")) >> Mkdir("/b"))
    val q = Atomic(Mkdir("/c") >> If(TestFileState("/a", DoesNotExist), Mkdir("/a"), Skip))
    assert(p.commutesWith(q))
  }
}
