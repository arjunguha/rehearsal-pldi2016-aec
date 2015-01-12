package fsmodel

import java.nio.file.Path

import Implicits._

class TypedZ3Tests extends org.scalatest.FunSuite {

  val z = new Z3Impl
  import z._
  // NOTE(kgeffen) Must be imported again after contents of z are imported
  // because TypedZ3 implicits are needed
  import Implicits._

  test("CheckSAT is true for true and not for false") {
    assert(checkSAT(true) == Some(true))
    assert(checkSAT(false) != Some(true))
  }

  test("Filestates are distinct") {
    assert(checkSAT(eq(isFile, isDir)) != Some(true))
    assert(checkSAT(eq(isFile, doesNotExist)) != Some(true))
  }

  test("And functions correctly for Z3Bools") {
    def checkAnd(a: Z3Bool, b: Z3Bool): Boolean =
      checkSAT(a && b) match {
        case Some(true) => true
        case _ => false
      }

    assert(checkAnd(true, true))
    assert(!checkAnd(true, false))
    assert(!checkAnd(false, true))
    assert(!checkAnd(false, false))
  }

  test("Or functions correctly for Z3Bools") {
    def checkOr(a: Z3Bool, b: Z3Bool): Boolean =
      checkSAT(a || b) match {
        case Some(true) => true
        case _ => false
      }

    assert(checkOr(true, true))
    assert(checkOr(true, false))
    assert(checkOr(false, true))
    assert(!checkOr(false, false))
  }

  test("Implies functions correctly for Z3Bools") {
    def checkImplies(a: Z3Bool, b: Z3Bool): Boolean =
      checkSAT(a --> b) match {
        case Some(true) => true
        case _ => false
      }

    assert(checkImplies(true, true))
    assert(!checkImplies(true, false))
    assert(checkImplies(false, true))
    assert(checkImplies(false, false))
  }

  test("Not functions correctly for Z3Bools") {
    def checkNot(a: Z3Bool): Boolean =
      checkSAT(!a) match {
        case Some(true) => true
        case _ => false
      }

    assert(!checkNot(true))
    assert(checkNot(false))
  }

  test("checkSAT not true for system with path consigned to multiple states") {
    val p = path("/")
    val fss = newState()

    assert(Some(true) !=
      checkSAT(and(testFileState(p, isDir, fss),
                   testFileState(p, isFile, fss))))
  }

  // TODO(kgeffen) Determine if this test works as intended and provides meaningful testing
  test("newState generates distinct state") {
    assert(newState != newState)
  }

}
