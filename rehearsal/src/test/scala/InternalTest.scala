import parser.Internal._

class InternalTestSuite extends org.scalatest.FunSuite {
  test("simplify attributes") {
    assert(
      simplifyAttributes(
        Seq(Attribute("require", ARes("File", "foo")), 
            Attribute("before", ARes("File", "bar"))
        ), 
        ARes("File", "bop")) 
      == (Seq(), Seq(Edge(ARes("File", "foo"), ARes("File", "bop")), 
                     Edge(ARes("File", "bop"), ARes("File", "bar")))))
  }

  test("desugar"){
    assert(desugar(Seq(Resource("foo", "file", Seq(Attribute("require", ARes("File", "bar")))))) ==
      Seq(Resource("foo", "file", Seq()), Edge(ARes("File", "bar"), ARes("File", "foo"))))
  }

}
