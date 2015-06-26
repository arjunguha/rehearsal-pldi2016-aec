trait WeakestPreconditionsTestSuite extends org.scalatest.fixture.FunSuite {
  import rehearsal.fsmodel._
  import FSSyntax._
  import WeakestPreconditions._

  case class FixtureParam(myBdd: bdd.Bdd[TestFileState]) {

    def wp(expr: Expr, pred: Pred): myBdd.Node = {
      wpBdd(myBdd)(expr, predToBdd(myBdd)(pred))
    }

    def fromPred(pred: Pred): myBdd.Node = {
      predToBdd(myBdd)(pred)
    }

    def checkBdd(node: myBdd.Node, pred: Pred): Unit = {
      val node2 = predToBdd(myBdd)(pred)
      val pred1 = bddToPred(myBdd)(node)
      assert(node == node2, s", i.e., ${pred1} != $pred")
    }
  }

  def withFixture(test: OneArgTest) = {
    val myBdd = bdd.Bdd[TestFileState]((x, y) => x < y)
    val theFixture = FixtureParam(myBdd)
    withFixture(test.toNoArgTest(theFixture))
  }

}

class SimpleWPTest extends WeakestPreconditionsTestSuite {
  import rehearsal.fsmodel._
  import FSSyntax._
  import Implicits._

  test("one mkdir") { arg =>
    import arg._

    checkBdd(wp(Mkdir("/foo"), True),
             TestFileState("/foo", DoesNotExist) && TestFileState("/", IsDir))
  }

  test("nested mkdir") { arg =>
    import arg._
    checkBdd(wp(Mkdir("/foo") >> Mkdir("/foo/bar"), True),
             TestFileState("/foo/bar", DoesNotExist) && TestFileState("/foo", DoesNotExist) &&
             TestFileState("/", IsDir))
  }

  test("mkdir with a strong postcondition") { arg =>
    import arg._
    checkBdd(wp(Mkdir("/foo"), TestFileState("/foo", IsDir)),
             TestFileState("/foo", DoesNotExist) && TestFileState("/", IsDir))
  }

}
