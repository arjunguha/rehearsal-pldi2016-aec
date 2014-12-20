package fsmodel

import java.nio.file.Path

import Implicits._

class TestSuite extends org.scalatest.FunSuite {

  val emptyState: Map[Path, FileState] = Map()
  val existingDir = "/pictures"
  // TODO(kgeffen) Improve this line
  val startState: Map[Path, FileState] = Map(stringToPath("/usr") -> IsDir,
                                             stringToPath("/usr/kai") -> IsDir,
                                             stringToPath(existingDir) -> IsDir,
                                             stringToPath("/usr/kai/config") -> IsFile)

  // TODO(kgeffen) Better title
  test("Error returns empty list of possible states") {
    assert(Eval.eval(Error, startState) == List())
  }

  test("Skip does not change state") {
    assert(Eval.eval(Skip, startState) == List(startState))
  }

  test("Mkdir creates file if parent exists and dir does not yet exist") {
    val newDir = existingDir + "/cats"

    assertResult(Eval.eval(Mkdir(newDir), startState)) {
      startState ++ Map(newDir -> IsDir)
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