import bdd._
import rehearsal.fsmodel._
import Implicits._
import WeakestPreconditions._

import java.nio.file.FileSystems

class PredConversionTests extends org.scalatest.FunSuite {
  test("negation normal form (nnf)") {
    val in = TestFileState(FileSystems.getDefault().getPath("/"), IsDir)
    assert((!(in && in)).nnf() == (!in || !in))
    assert((!(in || in)).nnf() == (!in && !in))
    assert((!(in || !in)).nnf() == (!in && in))
  }

  test("conjunctive normal form (cnf)") {
    val in = TestFileState(FileSystems.getDefault().getPath("/"), IsDir)
    assert((!(in || in)).cnf() == (!in && !in))
    assert((in && in || in).cnf() == ((in || in) && (in || in)))
    assert((in && (in || (in && in))).cnf() == (in && ((in || in) && (in || in))))
    assert((in || ((in || in) && in)).cnf() == ((in || (in || in)) && (in || in)))
  }

  test("predicate replace") {
    assert((And(False, False)).replace(False, True) == (And(True, True)))
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
