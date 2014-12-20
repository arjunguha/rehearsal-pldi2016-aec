package fsmodel

import java.nio.file.Path

import Implicits._
import Eval._

class TestSuite extends org.scalatest.FunSuite {

  val rootDir: Path = "/root"
  val startFile: Path = rootDir + "/README.txt"
  val emptyDir: Path = rootDir + "/empty"
  val nonexDir: Path = rootDir + "/unicorn"
  val startState: Map[Path, FileState] = Map(rootDir -> IsDir,
                                             startFile -> IsFile,
                                             emptyDir -> IsDir)

  // TODO(kgeffen) Better title
  test("Error returns empty list of possible states") {
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

  test("can constuct expressions") {

    Cp("/tmp/foo", "/home/kai/foo")

  }


  test("can constuct sequences") {

    val e = Block(Cp("/tmp/foo", "/home/kai/foo"),
                  Mv("/home/kai/foo", "/home/kai/bar"),
                  Mv("/home/kai/foo", "/home/kai/bar"))

  }

  test("can write predicates") {

    val a = !TestFileState("/foo", IsFile) && TestFileState("/bar", IsFile)
    println(a)

  }

}