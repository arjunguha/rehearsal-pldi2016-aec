package fsmodel

import java.nio.file.Path

import Implicits._
import Z3Eval._

class TypedZ3Tests extends org.scalatest.FunSuite {

  val z = new Z3Impl
  import z._
  // NOTE(kgeffen) Implicits must be imported again after contents of z are imported
  // because TypedZ3 implicits are needed
  import Implicits._

  test("True is SAT, false is not") {
    assert(checkSAT(true) == Some(true))
    assert(checkSAT(false) == Some(false))
  }

  test("Filestates are distinct") {
    assert(checkSAT(z.eq(isFile, isDir)) == Some(false))
    assert(checkSAT(z.eq(isFile, doesNotExist)) == Some(false))
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

  test("Given fileSystemState cannot have path be in multiple fileStates") {
    val p = path("/")
    val fss = newState

    assert(Some(false) ==
      checkSAT(and(testFileState(p, isDir, fss),
                   testFileState(p, isFile, fss))))
  }

  test("Multiple paths can have same fileState") {
    val p1 = path("/1")
    val p2 = path("/2")
    val fss = newState

    assert(Some(true) == 
      checkSAT(and(testFileState(p1, isDir, fss),
                   testFileState(p2, isDir, fss)))
      )
  }

  test("Distinct fileSystemStates can have different values for same path") {
    val p = path("/")
    val fss1 = newState
    val fss2 = newState

    assert(Some(true) == 
      checkSAT(and(testFileState(p, isDir, fss1),
                   testFileState(p, isFile, fss2)))
      )
  }

  test("Excluded middle") {
    val a = newBool
    assert(checkSAT(!(a || !a)) == Some(false))
  }

  // TODO(kgeffen) Include more tests like excluded middle

  import z3.scala._
  import z3.scala.dsl._
  import z3.scala.dsl.Operands._
  private val cxt = new Z3Context(new Z3Config("MODEL" -> true,
                                                 "TIMEOUT" -> 3000))

  test("evalR scratch") {
    assertResult(Some(false)) {
      evalR(Skip,
        cxt.mkStore(newState, path("/"), doesNotExist),
        cxt.mkStore(newState, path("/"), isDir))
      }

    // The above assertion does not error, the below error's loudly
    // when run twice even if Mkdir case undefined. (sbt > test > test)

    // assertResult(Some(true)) {
    // evalR(Mkdir("/foo"),
    //   cxt.mkStore(newState, path("/foo"), doesNotExist),
    //   cxt.mkStore(newState, path("/foo"), isDir))
    // }
  }

}
