package fsmodel

import java.nio.file.Path

import Implicits._
import Eval._

class TestSuite extends org.scalatest.FunSuite {

  val rootDir: Path = "/"
  val startFile: Path = rootDir + "/README.txt"
  val startFile2: Path = rootDir + "/cat.gif"
  val emptyDir: Path = rootDir + "/empty"
  val nonexDir: Path = rootDir + "/nonexDir"
  val nonexFile: Path = rootDir + "/nonexFile"
  val startState: State = Map(rootDir -> IsDir,
                              startFile -> IsFile,
                              startFile2 -> IsFile,
                              emptyDir -> IsDir)

  test("Eval(Error) returns empty list of possible states") {
    assert(eval(Error, startState) == List())
  }

  test("Skip does not change state") {
    assert(eval(Skip, startState) == List(startState))
  }

  test("Mkdir creates dir if parent exists and dir does not") {
    assertResult(
      List(startState + (nonexDir -> IsDir))
      ) {
      eval(Mkdir(nonexDir), startState)
    }
  }

  test("Mkdir fails when parent does not exist") {
    val newDir = nonexDir + "/new"

    assertResult(List()) {
      eval(Mkdir(newDir), startState)
    }
  }

  test("Mkdir fails when dir already exists") {
    assertResult(List()) {
      eval(Mkdir(rootDir), startState)
    }
  }

  test("CreateFile succeeds when parent dir exists and file does not") {
    val newFile: Path = rootDir + "/new.jpg"

    assertResult(
      List(startState + (newFile -> IsFile))
      ) {
      eval(CreateFile(newFile), startState)
    }
  }

  test("CreateFile fails when parent dir does not exist") {
    val newFile = nonexDir + "/food.jpg"

    assertResult(List()) {
      eval(CreateFile(newFile), startState)
    }
  }

  test("CreateFile fails when file already exists") {
    assertResult(List()) {
      eval(CreateFile(startFile), startState)
    }
  }

  test("Rm removes file when it exists") {
    assertResult(
      List(startState - startFile)
      ) {
      eval(Rm(startFile), startState)
    }
  }

  test("Rm removes folder when it exists and is empty") {
    assertResult(
      List(startState - emptyDir)
      ) {
      eval(Rm(emptyDir), startState)
    }
  }

  test("Rm fails to remove nonexistant dir") {
    assertResult(List()) {
      eval(Rm(nonexDir), startState)
    }
  }

  test("Rm fails to remove filled dir") {
    assertResult(List()) {
      eval(Rm(rootDir), startState)
    }
  }

  test("Cp copies file when src exists, dst does not, & dst's dir does") {
    val dst: Path = emptyDir + "/new.txt"

    assertResult(
      List(startState + (dst -> IsFile))
      ) {
      eval(Cp(startFile, dst), startState)
    }
  }

  test("Cp fails when src is a dir") {
    assertResult(List()) {
      eval(Cp(emptyDir, nonexDir), startState)
    }
  }

  test("Cp fails when src does not exist") {
    val dst = rootDir + "/new.txt"

    assertResult(List()) {
      eval(Cp(nonexFile, dst), startState)
    }
  }

  test("Cp fails when dst already exists") {
    assertResult(List()) {
      eval(Cp(startFile, startFile2), startState)
    }
  }

  test("Cp fails when dst's parent does not exist") {
    val dst = nonexDir + "/new.txt"

    assertResult(List()) {
      eval(Cp(startFile, dst), startState)
    }
  }

  test("Mv moves file when src exists, dst does not, & dst's dir does") {
    assertResult(
      List(startState - startFile + (nonexFile -> IsFile))
      ) {
      eval(Mv(startFile, nonexFile), startState)
    }
  }

  test("Mv fails when src does not exist") {
    val dst = rootDir + "/new.jpg"

    assertResult(List()) {
      eval(Mv(nonexFile, dst), startState)
    }
  }

  test("Mv fails when dst already exists") {
    assertResult(List()) {
      eval(Mv(startFile, startFile2), startState)
    }
  }

  test("Mv fails when dst's parent does not exist") {
    val dst = nonexDir + "/new.txt"

    assertResult(List()) {
      eval(Mv(startFile, dst), startState)
    }
  }

  test("Mv moves empty dir when src exists, dst does not, dst's parent does") {
    assertResult(
      List(startState - emptyDir + (nonexDir -> IsDir))
      ) {
      eval(Mv(emptyDir, nonexDir), startState)
    }
  }

  test("Mv moves dir and its contents") {
    val childDirStart: Path = emptyDir + "/newDir"
    val childDirEnd: Path = nonexDir + "/newDir"
    val outerFileStart: Path = emptyDir + "/1.jpg"
    val outerFileEnd: Path = nonexDir + "/1.jpg"
    val innerFileStart: Path = childDirStart + "/2.jpg"
    val innerFileEnd: Path = childDirEnd + "/2.jpg"

    assertResult(
      List(startState - emptyDir + (nonexDir -> IsDir) + (childDirEnd -> IsDir) +
        (outerFileEnd -> IsFile) + (innerFileEnd -> IsFile))
      ) {
      eval(Block(Mkdir(childDirStart),
                 CreateFile(outerFileStart),
                 CreateFile(innerFileStart),
                 // emptyDir now contains a file and a dir with a file
                 Mv(emptyDir, nonexDir)),
           startState)
    }
  }

  test("Mv fails to move a dir within itself") {
    assertResult(List()) {
      eval(Mv(rootDir, nonexDir), startState)
    }
  }

  test("Block mkdir, remove dir returns start state") {
    assertResult(List(startState)) {
      eval(Block(Mkdir(nonexDir),
                 Rm(nonexDir)),
           startState)
    }
  }

  test("Block create file, cp, remove file returns state with copied file") {
    val dst: Path = rootDir + "/new.jpg"

    assertResult(
      List(startState + (dst -> IsFile))
      ) {
      eval(Block(CreateFile(nonexFile),
                 Cp(nonexFile, dst),
                 Rm(nonexFile)),
           startState)
    }
  }

  test("Block removing dir before making it fails") {
    assertResult(List()) {
      eval(Block(Rm(nonexDir),
                 Mkdir(nonexDir)),
           startState)
    }
  }

  test("Block making same dir twice fails") {
    assertResult(List()) {
      eval(Block(Mkdir(nonexDir),
                 Mkdir(nonexDir)),
           startState)
    }
  }

  test("Alt returns both possible states for 2 distinct valid operations") {
    val newDir: Path = emptyDir + "/new"
    val res = eval(Alt(Rm(startFile),
                       Mkdir(newDir)),
                   startState)
    assert(res.contains(startState - startFile))
    assert(res.contains(startState + (newDir -> IsDir)))
    assert(res.length == 2)
  }

  test("Alt returns only state from non-failing expression") {
    assertResult(
      List(startState - startFile)
      ) {
      eval(Alt(Rm(startFile),
               Rm(nonexDir)),
           startState)
    }
  }

  test("Alt twice with valid distinct exprs results in 4 states") {
    val res = eval(Block(Alt(Mkdir(emptyDir + "/1"), Mkdir(emptyDir + "/2")),
                         Alt(Mkdir(emptyDir + "/a"), Mkdir(emptyDir + "/b"))),
                   startState)
    assert(res.length == 4)
  }

  test("If True runs first expression") {
    assertResult(List()) {
      eval(If(True,
              Error,
              Skip),
           startState)
    }
  }

  test("If False runs second expression") {
    assertResult(List()) {
      eval(If(False,
              Skip,
              Error),
           startState)
    }
  }

  test("If Not behaves like unless") {
    assertResult(List()) {
      eval(If(!True, Skip, Error), startState)
    }
    assertResult(List()) {
      eval(If(!False, Error, Skip), startState)
    }
  }

  test("If And is true only when both predicates are true") {
    def evalAnd(p1: Pred, p2: Pred): Boolean = {
      eval(If(p1 && p2, Error, Skip), startState) == List()
    }
    assert(evalAnd(True, True))
    assert(!evalAnd(True, False))
    assert(!evalAnd(False, True))
    assert(!evalAnd(False, False))
  }

  test("If Or is false only when both predicates are false") {
    def evalOr(p1: Pred, p2: Pred): Boolean = {
      eval(If(p1 || p2, Error, Skip), startState) == List()
    }
    assert(!evalOr(False, False))
    assert(evalOr(True, False))
    assert(evalOr(False, True))
    assert(evalOr(True, True))
  }

  test("TestFileState correctly identifies IsFile, IsDir, DoesNotExist in static state") {
    def evalFileStateMatch(path: Path, s: FileState): Boolean = {
      eval(If(TestFileState(path, s), Error, Skip), startState) == List()
    }
    assert(evalFileStateMatch(emptyDir, IsDir))
    assert(evalFileStateMatch(startFile, IsFile))
    assert(evalFileStateMatch(nonexDir, DoesNotExist))
  }

  test("TestFileState identifies nonexistance of file after being removed") {
    assertResult(List()) {
      eval(Block(Rm(emptyDir),
                 If(TestFileState(emptyDir, DoesNotExist),
                    Error, Skip)),
           startState)
    }
  }

  test("TestFileState identifies type for path whose type changed") {
    assertResult(List()) {
      eval(Block(Rm(startFile),
                 Mkdir(startFile),
                 If(TestFileState(emptyDir, IsDir),
                    Error, Skip)),
           startState)
    }
  }

  // NOTE(kgeffen) Except in case when expr causes error
  test("evalR is eval's identity function") {
    val exprs = List(Skip,
                     Mkdir(nonexDir),
                     CreateFile(nonexFile),
                     Cp(startFile, nonexFile),
                     Mv(emptyDir, nonexDir),
                     Mv(startFile, nonexFile),
                     Rm(startFile),
                     Rm(emptyDir),
                     Alt(CreateFile(nonexFile), Mkdir(nonexDir)),
                     Alt(Rm(rootDir), Rm(emptyDir)),  // first expr will fail because dir filled
                     // Rm(rootDir) should fail but isn't reached
                     If(TestFileState(emptyDir, IsDir), Rm(emptyDir), Rm(rootDir)),
                     If(TestFileState(emptyDir, IsFile), Rm(rootDir), Rm(emptyDir)),
                     Block(CreateFile(nonexFile), Rm(nonexFile)),
                     Block(Rm(startFile), Rm(emptyDir))
                     )
    assert(exprs.forall(evalIdentityHolds(_)))
  }

  def evalIdentityHolds(expr: Expr): Boolean = {
    val endStates = eval(expr, startState)
    if(endStates.length > 0)
      evalR(expr, startState, endStates.head)
    else
      false
  }

}
