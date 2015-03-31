import eval._
import eval.Implicits._
import Ample._

class CountFinalTests extends org.scalatest.FunSuite {

  // TODO(arjun): I'm not sure how to properly test unconcur
  test("atomic * atomic") {
    val e = Mkdir("/a") * Mkdir("/b")
    assert(finalStates(makeGraph(initState, e)).size == 1)
  }

  test(">> * atomic") {
    val e = (Mkdir("/a") >> Mkdir("/b")) * Mkdir("/c")
    assert(makeGraph(initState, e).nodes.size == 2)
  }

  test("(p>>q) * (r>>s)") {
    val p = Mkdir("/a")
    val r = Mkdir("/b")
    val q = If(TestFileState("/b", IsDir), Skip, Skip)
    val s = If(TestFileState("/a", IsDir), Skip, Skip)

    // Below, the LHS writes /a and reads /b and the RHS writes /b and reads
    // /a, so the two sides do not (syntactically) commute. Naively,
    // we would generate the five interleavings:
    //
    //   pqrs, prqs, prsq, rpsq, rspq, rpsq
    //
    // However, note that p and r commute and q and s commute. Therefore, the
    // following identities hold:
    //
    //   prqs = prsq (q and s commute syntactically)
    //   prsq = rpsq (p and r commute syntactically)
    //   rpsq = rpqs (p and r commute syntactically)
    //
    // Which leaves pqrs and rspq
    //
    // Perhaps we only need to generate three paths?
    val e = (p >> q) * (r >> s)
    val g = makeGraph(initState, e)

    println(drawGraph(e))
    assert(g.nodes.size == 2)


  }

  test("nested stars") {
    val e = (Mkdir("/a") * Mkdir("/b")) * Mkdir("/c")
    assert(finalStates(makeGraph(initState, e)).size == 1)
  }

}
