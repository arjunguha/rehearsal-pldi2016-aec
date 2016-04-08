class ResearchMethodsSuite extends FunSuitePlus
  with org.scalatest.BeforeAndAfterEach {

  import rehearsal._
  import PuppetParser.parseFile
  import rehearsal.Implicits._
  import SymbolicEvaluator.{predEquals, exprEquals, isDeterministic, isDeterministicError}
  import PuppetSyntax._

  val root = "researchMethodsTests"

  override def beforeEach() = {
    FSSyntax.clearCache()
  }

  test("dhoppe-monit.pp - ubuntu") {
    val g = parseFile(s"$root/dhoppe-monit.pp").eval.resourceGraph.fsGraph("ubuntu-trusty")
    assert(SymbolicEvaluator.isDeterministic(g) == true)
  }

  test("dhoppe-monit_BUG.pp - ubuntu") {
    val g = parseFile(s"$root/dhoppe-monit_BUG.pp").eval.resourceGraph.fsGraph("ubuntu-trusty")
    assert(SymbolicEvaluator.isDeterministicError(g) == true)
  }

  test("dhoppe-monit.pp - centos") {
    val g = parseFile(s"$root/dhoppe-monit.pp").eval.resourceGraph.fsGraph("centos-6")
    assert(SymbolicEvaluator.isDeterministic(g) == true)
  }

  test("dhoppe-monit_BUG.pp - centos") {
    val g = parseFile(s"$root/dhoppe-monit_BUG.pp").eval.resourceGraph.fsGraph("centos-6")
    assert(SymbolicEvaluator.isDeterministicError(g) == true)
  }

}
