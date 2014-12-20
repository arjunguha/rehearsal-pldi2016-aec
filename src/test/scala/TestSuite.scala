package fsmodel

import java.nio.file.Path

import Implicits._
import Eval._

class TestSuite extends org.scalatest.FunSuite {

  val emptyState: Map[Path, FileState] = Map()
  val existingDir = "pictures/"
  val existingFile = existingDir + "README.txt"
  // TODO(kgeffen) Improve this line
  val startState: Map[Path, FileState] = Map(stringToPath(existingDir) -> IsDir,
                                             stringToPath(existingFile) -> IsFile)

  // TODO(kgeffen) Better title
  test("Error returns empty list of possible states") {
    assert(eval(Error, startState) == List())
  }

  test("Skip does not change state") {
    assert(eval(Skip, startState) == List(startState))
  }

  test("Mkdir creates dir if parent exists and dir does not") {
    val newDir: Path = existingDir + "cats"

    assertResult(
      List(startState + (newDir -> IsDir))
      ) {
      eval(Mkdir(newDir), startState)
    }
  }

  test("Mkdir fails when parent does not exist") {
    val newDir = existingDir + "/nonExistantDir/cats"

    assertResult(List()) {
      eval(Mkdir(newDir), startState)
    }
  }

  test("Mkdir fails when dir already exists") {
    assertResult(List()) {
      eval(Mkdir(existingDir), startState)
    }
  }

  test("CreateFile succeeds when parent dir exists and file does not") {
    val newFile: Path = existingDir + "new.jpg"

    assertResult(
      List(startState + (newFile -> IsFile))
      ) {
      eval(CreateFile(newFile), startState)
    }
  }

  test("CreateFile fails when parent dir does not exist") {
    val newFile = existingDir + "/nonExistantDir/food.jpg"

    assertResult(List()) {
      eval(CreateFile(newFile), startState)
    }
  }

  test("CreateFile fails when file already exists") {
    assertResult(List()) {
      eval(CreateFile(existingFile), startState)
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