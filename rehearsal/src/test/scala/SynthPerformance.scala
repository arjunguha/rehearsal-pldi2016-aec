import rehearsal.UpdateSynth._

class SynthPerformance extends org.scalatest.FunSuite {
  def uncurry[A, B, C](f: (A, B) => C)(t: (A, B)): C = f(t._1, t._2)

  0.to(5).map(x => {
    val start = java.lang.System.currentTimeMillis()
    uncurry(execLists)(gen(x))
    val end = java.lang.System.currentTimeMillis()
    println(s"$x\t${end - start}")
  })
}
