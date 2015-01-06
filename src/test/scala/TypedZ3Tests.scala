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
    assert(checkSAT(isFile == isDir) != Some(true))
    assert(checkSAT(isFile == doesNotExist) != Some(true))
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

  test("checkSAT(true) is true") {
    assert(checkSAT(true) == Some(true))
  }

  test("checkSAT not trueue for system with path consigned to multiple states") {
    val p = path("/")
    val fss = newState()

    assert(Some(true) !=
      checkSAT(and(testFileState(p, isDir, fss),
                       testFileState(p, isFile, fss))))
  }

  test("newState generates distinct state") {
    assert(newState != newState)
  }

  // test("f") {
  //   assert(z.checkSAT(z.isFile == z.isDir) == None)
  // }

}
