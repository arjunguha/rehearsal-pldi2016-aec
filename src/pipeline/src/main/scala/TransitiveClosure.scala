object TransitiveClosure {

  // one transitive step
  private def addTransitive[A, B](s: Set[(A, B)]) = {
    s ++ (for ((x1, y1) <- s; (x2, y2) <- s if y1 == x2) yield (x1, y2))
  }

  //repeat until we don't get a bigger set
  def apply[A,B](s:Set[(A,B)]):Set[(A,B)] = {
    val t = addTransitive(s)
    if (t.size == s.size) s else TransitiveClosure(t)
  }

  def test() {
    println(TransitiveClosure(Set((1,2), (2,3), (3,4))))
  }
}
