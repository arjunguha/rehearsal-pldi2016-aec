class FSBDDTests extends org.scalatest.FunSuite with org.scalatest.Matchers {

  import rehearsal._
  import Implicits._
  import FSSyntax.{testFileState, IsFile, IsDir, DoesNotExist}

  implicit object Int2SemiRing extends SemiRing[Int] {

    val zero = 0
    val one = 1
    def mul(x: Int, y: Int) = x * y
    def sum(x: Int, y: Int) = if (x == 1 || y == 1) 1 else 0

  }

  test("leaf nodes are cached correctly") {
    val dd = FSBDD[Int]
    import dd._

    assert(Leaf(0) eq Leaf(0))
    assert(Leaf(1) eq Leaf(1))
    assert((Leaf(0) eq Leaf(1)) == false)
  }

  test("branches cached correctly") {
    val dd = FSBDD[Int]
    import dd._
    assert(Branch(testFileState("/x", IsFile), Leaf(0), Leaf(1)) eq
      Branch(testFileState("/x", IsFile), Leaf(0), Leaf(1)))

  }

  test("mkTest correct") {
    val dd = FSBDD[Int]
    import dd._
    val t = Branch(testFileState("/x", IsFile), Leaf(0), Leaf(1))
    assert(t.restrict(testFileState("/x", IsFile), true) eq Leaf(1))
    assert(t.restrict(testFileState("/x", IsFile), false) eq Leaf(0))
  }

  test("restrict is consistent with apply") {
    val dd = FSBDD[Int]
    import dd._
    val r = Branch(testFileState("/x", IsFile), Leaf(0), Leaf(1))
    val s = Branch(testFileState("/y", IsFile), Leaf(0), Leaf(1))
    val t = r.applyOp(s){ (x, y) => x * y }

    assert(t.restrict(testFileState("/x", IsFile), true).restrict(testFileState("/y", IsFile), true) eq Leaf(1))

  }

  test("apply operator simplifies file-state tests") {
    val dd = FSBDD[Int]
    import dd._
    val r = Branch(testFileState("/x", IsFile), Leaf(0), Leaf(1))
    val s = Branch(testFileState("/x", IsDir), Leaf(0), Leaf(1))
    val t = r.applyOp(s) {
      case (_, 1) => 1
      case (1, _) => 1
      case (0, 0) => 0
      case (_, _) => throw Unexpected("impossible")
    }
    assert(t.restrict(testFileState("/x", IsFile), true) eq Leaf(1))

  }

  test("conjunction of two mutually exclusive states is 0") {
    val dd = FSBDD[Int]
    import dd._
    val r = Branch(testFileState("/x", IsFile), Leaf(0), Leaf(1))
    val s = Branch(testFileState("/x", IsDir), Leaf(0), Leaf(1))
    val t = r.applyOp(s)((x, y) => x * y)
    assert(t  eq Leaf(0))

  }
}
