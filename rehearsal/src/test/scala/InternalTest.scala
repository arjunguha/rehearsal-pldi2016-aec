import parser.Internal._

class InternalTestSuite extends org.scalatest.FunSuite {
  test("simplify attributes") {
    val initattrs = Seq(Attribute("require", ARes("File", "foo")), 
            Attribute("before", ARes("File", "bar")))
    val curRes = ARes("File", "bop")
    val edge1 = Edge(ARes("File","foo"),ARes("File","bop"))
    val edge2 = Edge(ARes("File","bop"),ARes("File","bar"))
    val newExprs = Block(edge1, Block(edge2,EmptyExpr))

    assert(simplifyAttributes(initattrs, curRes) == (Seq(), newExprs))
  }

  test("desugar"){
    val prog = Block(Resource(AString("foo"), "file", Seq(Attribute("require", ARes("File", "bar")))),
                     EmptyExpr)
    val res = Block(Block(Resource(AString("foo"), "file", Seq()), 
                          Block(Edge(ARes("File", "bar"), ARes("File", "foo")), EmptyExpr)), 
                    EmptyExpr)

    assert(desugar(prog) == res)
  }

}
