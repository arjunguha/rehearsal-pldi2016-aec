package fsmodel

import java.nio.file.Path

import Implicits._

class TypedZ3Tests extends org.scalatest.FunSuite {

  val z = new Z3Impl
  val tr = z.z3true
  val fa = z.z3false

  test("Z3Bools are distinct") {
    assert(tr != fa)
  }

  test("Z3FileStates are distinct") {
    assert(z.isFile != z.isDir)
    assert(z.isFile != z.doesNotExist)
  }

  test("And functions correctly for Z3Bools") {
    assert(tr == z.and(tr, tr))
    assert(fa == z.and(tr, fa))
    assert(fa == z.and(fa, tr))
    assert(fa == z.and(fa, fa))
  }

  test("Or functions correctly for Z3Bools") {
    assert(fa == z.or(fa, fa))
    assert(tr == z.or(tr, fa))
    assert(tr == z.or(fa, tr))
    assert(tr == z.or(tr, tr))
  }

  test("Implies functions correctly for Z3Bools") {
    assert(fa == z.implies(tr, fa))
    assert(tr == z.implies(tr, tr))
    assert(tr == z.implies(fa, tr))
    assert(tr == z.implies(fa, fa))
  }

  test("Not works for Z3Bools") {
    assert(z.not(tr) == fa)
    assert(z.not(fa) == tr)
  }

  test("checkSAT true for trivial cases") {
    assert(z.checkSAT(tr) == Some(true))
    assert(z.checkSAT(fa) == Some(true))
  }

  test("checkSAT not true for system with path consigned to multiple states") {
    val p = z.path("/")
    val fss = z.newState()

    assert(Some(true) !=
      z.checkSAT(z.and(z.testFileState(p, z.isDir, fss),
                       z.testFileState(p, z.isFile, fss))))
  }

  test("newState generates distinct state") {
    assert(z.newState != z.newState)
  }

}
