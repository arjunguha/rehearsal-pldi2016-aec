package fsmodel

import java.nio.file.Path

import Implicits._
import Z3Eval._

class TypedZ3Tests extends org.scalatest.FunSuite {

  import Z3Eval.z._
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

  test("evalR Error unSAT") {
    assertResult(Some(false)) {
      checkSAT(evalR(Error, newState, newState))
    }
  }

  test("evalR Skip SAT") {
    assertResult(Some(true)) {
      checkSAT(evalR(Skip, newState, newState))
    }
  }

  test("evalR Mkdir SAT for newStates") {
    assertResult(Some(true)) {
      checkSAT(evalR(Mkdir("/"), newState, newState))
    }
  }

  test("evalR Mkdir unSAT when dst already exists") {
    assertResult(Some(false)) {
      checkSAT(evalR(Block(Mkdir("/"), Mkdir("/")), newState, newState))
    }
    assertResult(Some(false)) {
      checkSAT(evalR(Block(CreateFile("/"), Mkdir("/")), newState, newState))
    }
  }

  test("evalR CreateFile SAT for newStates") {
    assertResult(Some(true)) {
      checkSAT(evalR(CreateFile("/"), newState, newState))
    }
  }

  test("evalR CreateFile unSAT when dst already exists") {
    assertResult(Some(false)) {
      checkSAT(evalR(Block(Mkdir("/"), CreateFile("/")), newState, newState))
    }
    assertResult(Some(false)) {
      checkSAT(evalR(Block(CreateFile("/"), CreateFile("/")), newState, newState))
    }
  }

  test("evalR Cp SAT for newStates") {
    assertResult(Some(true)) {
      checkSAT(evalR(Cp("/src", "/dst"), newState, newState))
    }
  }

  test("evalR Cp unSAT when src is dir") {
    assertResult(Some(false)) {
      checkSAT(evalR(Block(Mkdir("/src"), Cp("/src", "/dst")),
                     newState, newState))
    }
  }

  test("evalR Cp unSAT when dst already exists") {
    assertResult(Some(false)) {
      checkSAT(evalR(Block(CreateFile("/dst"), Cp("/src", "/dst")),
                     newState, newState))
    }
    assertResult(Some(false)) {
      checkSAT(evalR(Block(Mkdir("/dst"), Cp("/src", "/dst")),
                     newState, newState))
    }
  }

  test("evalR Alt Skip Error is SAT") {
    assertResult(Some(true)) {
      checkSAT(evalR(Alt(Error, Skip), newState, newState))
    }
    assertResult(Some(true)) {
      checkSAT(evalR(Alt(Skip, Error), newState, newState))
    }
  }

  test("evalR If acts correctly for true, false") {
    assertResult(Some(true)) {
      checkSAT(evalR(If(False, Error, Skip),
               newState, newState))
    }
    assertResult(Some(true)) {
      checkSAT(evalR(If(True, Skip, Error),
               newState, newState))
    }
  }

  test("newState does not consign paths to states") {
    assertResult(Some(true)) {
      checkSAT(evalR(If(TestFileState("/", IsDir),
                        Error, Skip),
               newState, newState))
    }
    assertResult(Some(true)) {
      checkSAT(evalR(If(TestFileState("/", IsFile),
                        Error, Skip),
               newState, newState))
    }
    assertResult(Some(true)) {
      checkSAT(evalR(If(TestFileState("/", DoesNotExist),
                        Error, Skip),
               newState, newState))
    }
  }

  test("evalR Rm SAT for newState") {
    assertResult(Some(true)) {
      checkSAT(evalR(Rm("/"), newState, newState))
    }
  }

  test("evalR Rm unSAT when dst does not exist") {
    assertResult(Some(false)) {
      checkSAT(evalR(Block(Mkdir("/"),
                           Rm("/"),
                           Rm("/")),
                     newState, newState))
    }
  }

  test("evalR Rm unSAT when dst is filled dir") {
    assertResult(Some(false)) {
      checkSAT(evalR(Block(Mkdir("/parent"),
                           Mkdir("/parent/child"),
                           Rm("/parent")),
                     newState, newState))
    }
  }

}
