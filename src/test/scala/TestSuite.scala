package fsmodel

import java.nio.file.Path

import Implicits._
import Eval._

class TestSuite extends org.scalatest.FunSuite {

  val rootDir: Path = "/root"
  val startFile: Path = rootDir + "/README.txt"
  val emptyDir: Path = rootDir + "/empty"
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
    val newDir: Path = rootDir + "/new"

    assertResult(
      List(startState + (newDir -> IsDir))
      ) {
      eval(Mkdir(newDir), startState)
    }
  }

  test("Mkdir fails when parent does not exist") {
    val newDir = rootDir + "/nonexistantDir/new/"

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
    val newFile = rootDir + "/nonExistantDir/food.jpg"

    assertResult(List()) {
      eval(CreateFile(newFile), startState)
    }
  }

  test("CreateFile fails when file already exists") {
    assertResult(List()) {
      eval(CreateFile(startFile), startState)
    }
  }

  test("Rm removes file if it exists") {
    assertResult(
      List(startState - startFile)
      ) {
      eval(Rm(startFile), startState)
    }
  }

  test("Rm removes folder if it exists and is empty") {
    assertResult(
      List(startState - emptyDir)
      ) {
      eval(Rm(emptyDir), startState)
    }
  }

  test("Rm fails to remove nonexistant file") {
    val nonexistant = rootDir + "/nonex.jpg"

    assertResult(List()) {
      eval(Rm(nonexistant), startState)
    }
  }

  test("Rm fails to remove filled dir") {
    assertResult(List()) {
      eval(Rm(rootDir), startState)
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