import rehearsal.UpdateSynth._

class SynthPerformance extends org.scalatest.FunSuite {
  def uncurry[A, B, C](f: (A, B) => C)(t: (A, B)): C = f(t._1, t._2)

  println("Grow manifest prefix")
  println("-=-=-=-=-=--=-=-=-=-")
  0.to(10).map(x => {
    val pre = genPrefix(x)
    val start = java.lang.System.currentTimeMillis()
    uncurry(execLists)(gen(3) match {
      case (a, b) =>  (pre ++ a, pre ++ b)
    })
    val end = java.lang.System.currentTimeMillis()
    println(s"$x\t${end - start}")
  })

  println("Grow second manifest")
  println("-=-=-=-=-=--=-=-=-=-")
  0.to(10).map(x => {
    val start = java.lang.System.currentTimeMillis()
    uncurry(execLists)(gen(0, x))
    val end = java.lang.System.currentTimeMillis()
    println(s"$x\t${end - start}")
  })

  println("Grow first manifest")
  println("-=-=-=-=-=-=--=-=-=")
  0.to(10).map(x => {
    val start = java.lang.System.currentTimeMillis()
    uncurry(execLists)(gen(x, 0))
    val end = java.lang.System.currentTimeMillis()
    println(s"$x\t${end - start}")
  })

  println("Grow both manifests")
  println("-=-=-=-=-=-=-=-=-=-")
  0.to(3).map(x => {
    val start = java.lang.System.currentTimeMillis()
    uncurry(execLists)(gen(x))
    val end = java.lang.System.currentTimeMillis()
    println(s"$x\t${end - start}")
  })
}
