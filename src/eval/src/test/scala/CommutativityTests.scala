import eval._
import eval.Implicits._
import Ample._

class CommutativityTests extends org.scalatest.FunSuite {

  test("idempotent directory creation") {
    val p = If(TestFileState("/parent", IsDir), Skip, Mkdir("/parent"))
    assert(p.readSet.size == 0)
    assert(p.writeSet.size == 0)
  }

}
