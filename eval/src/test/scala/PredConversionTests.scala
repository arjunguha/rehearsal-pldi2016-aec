import eval._

import java.nio.file.FileSystems

class PredConversionTests extends org.scalatest.FunSuite {
  test("negation normal form (nnf)") {
    assert(Not(And(True, False)).nnf() == Or(Not(True), Not(False)))
    assert(Not(Or(True, False)).nnf() == And(Not(True), Not(False)))
    assert(Not(Or(True, Not(False))).nnf() == And(Not(True), False))
  }

  test("conjunctive normal form (cnf)") {
    assert(Not(Or(True, False)).cnf() == And(Not(True), Not(False)))
    assert(Or(And(True, True), False).cnf() == And(Or(True, False), Or(True, False)))
    assert(And(True, Or(False, And(True, True))).cnf() == And(True, And(Or(False, True), 
                                                                        Or(False, True))))
    assert(Or(True, And(Or(True, False), False)).cnf() == And(Or(True, Or(True,False)), 
                                                              Or(True,False)))
  }

  test("predicate replace") {
    assert(And(False, False).replace(False, True) == And(True, True))
    assert(And(Or(False, True), Or(False, False)).replace(Or(False, False), False) ==
           And(Or(False, True), False))
    val isdir = TestFileState(FileSystems.getDefault().getPath("/home"), IsDir)
    assert(And(True, isdir).replace(isdir, False) == And(True, False))
  }
}
