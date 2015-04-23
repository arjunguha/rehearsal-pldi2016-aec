import eval._
import eval.Implicits._

import java.nio.file.FileSystems

class PredConversionTests extends org.scalatest.FunSuite {
  test("negation normal form (nnf)") {
    assert((!(True && False)).nnf() == (!True || !False))
    assert((!(True || False)).nnf() == (!True && !False))
    assert((!(True || !False)).nnf() == (!True && False))
  }

  test("conjunctive normal form (cnf)") {
    assert((!(True || False)).cnf() == (!True && !False))
    assert((True && True || False).cnf() == ((True || False) && (True || False)))
    assert((True && (False || (True && True))).cnf() == (True && ((False || True) &&
                                                         (False || True))))
    assert((True || ((True || False) && False)).cnf() == ((True || (True || False)) &&
                                                          (True || False)))
  }

  test("predicate replace") {
    assert((False && False).replace(False, True) == (True && True))
    assert(((False || True) && (False || False)).replace((False || False), False) ==
           ((False || True) && False))
    val isdir = TestFileState(FileSystems.getDefault().getPath("/home"), IsDir)
    assert((True && isdir).replace(isdir, False) == (True && False))
  }

  test("weakest precondition (wp)") {
    val hash = (for (i <- 0 until 16) yield 0.toByte).toArray
    val root = FileSystems.getDefault().getPath("/")
    val home = FileSystems.getDefault().getPath("/home")
    assert(Mkdir(home).wp(TestFileState(home, IsDir)) == (True &&
      (TestFileState(home, DoesNotExist) && TestFileState(root, IsDir))))
    assert(CreateFile(home, hash).wp(TestFileState(home, IsDir)) == (False &&
           (TestFileState(home, DoesNotExist) && TestFileState(root, IsDir))))
    assert(Seq(Skip, Skip).wp(True) == True)
  }
}
