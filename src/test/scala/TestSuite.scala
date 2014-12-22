package fsmodel

import java.nio.file.Path

import Implicits._
import Eval._

class TestSuite extends org.scalatest.FunSuite {

  val rootDir: Path = "/root"
  val startFile: Path = rootDir + "/README.txt"
  val emptyDir: Path = rootDir + "/empty"
  val nonexDir: Path = rootDir + "/unicorn"
  val startState: State = Map(rootDir -> IsDir,
                              startFile -> IsFile,
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

  test("Cp copies file when src exists, target does not, & target's dir does") {
    val target: Path = emptyDir + "/new.txt"

    assertResult(
      List(startState + (target -> IsFile))
      ) {
      eval(Cp(startFile, target), startState)
    }
  }

  test("Cp fails when src does not exist") {
    val target = rootDir + "/new"

    assertResult(List()) {
      eval(Cp(nonexDir, target), startState)
    }
  }

  test("Cp fails when target already exists") {
    assertResult(List()) {
      eval(Cp(rootDir, emptyDir), startState)
    }
  }

  test("Cp fails when target's parent does not exist") {
    val target = nonexDir + "/new.txt"

    assertResult(List()) {
      eval(Cp(startFile, target), startState)
    }
  }

  test("Mv moves file when src exists, target does not, & target's dir does") {
    val target: Path = emptyDir + "/new.txt"

    assertResult(
      List(startState - startFile + (target -> IsFile))
      ) {
      eval(Mv(startFile, target), startState)
    }
  }

  test("Mv fails when src does not exist") {
    val target = rootDir + "/new"

    assertResult(List()) {
      eval(Mv(nonexDir, target), startState)
    }
  }

  test("Mv fails when target already exists") {
    assertResult(List()) {
      eval(Mv(rootDir, emptyDir), startState)
    }
  }

  test("Mv fails when target's parent does not exist") {
    val target = nonexDir + "/new.txt"

    assertResult(List()) {
      eval(Mv(startFile, target), startState)
    }
  }

  test("Block mkdir, remove dir returns start state") {
    assertResult(List(startState)) {
      eval(Block(Mkdir(nonexDir),
                 Rm(nonexDir)),
           startState)
    }
  }

  test("Block mkdir, cp, remove dir returns state with copied dir") {
    val target: Path = rootDir + "/new"

    assertResult(
      List(startState + (target -> IsDir))
      ) {
      eval(Block(Mkdir(nonexDir),
                 Cp(nonexDir, target),
                 Rm(nonexDir)),
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

}
