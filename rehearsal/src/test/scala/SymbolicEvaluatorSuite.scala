import rehearsal.fsmodel._
import Implicits._

class SymbolicEvaluatorSuite extends org.scalatest.FunSuite {

  // test("test choices") {

  //   val eval = new SymbolicEvaluatorImpl()
  //   import eval._

  //   assert(eval.isSAT(notB(eqB(choices(List(trueB, falseB)),
  //                              choices(List(trueB, falseB))))))

  // }

  test("test hash codes") {

    val eval = SymbolicEvaluator(false)
    import eval._

    val formula = fresh { st =>
      matchST(st, trueB) { fs =>
        testFileHashB(setFileHash(fs, "/foo", Array.fill(16)(1)),
                          "/foo",
                          Array.fill(16)(1))
      }
    }

    assert(check(notB(formula)) == Unsat)
  }

  // test("test choices with paths") {

  //   val eval = SymbolicEvaluator(false)
  //   import eval._

  //   val formula = fresh { st =>
  //     def expr() = matchST(st, error) { fs =>
  //       ok(choices(List(update(fs, "/foo", IsDir),
  //                       update(fs, "/bar", IsDir))))
  //     }
  //     eqB(expr(), expr())
  //   }

  //   assert(check(notB(formula)) == Unsat)
  // }

}