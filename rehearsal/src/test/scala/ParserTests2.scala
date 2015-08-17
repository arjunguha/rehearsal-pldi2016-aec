import parser.Syntax2._

class ParserTestSuite2 extends org.scalatest.FunSuite {
	test("just checking"){
		val prog: Manifest = Edge(Var("x"), Empty)
		assert(prog == prog)
	}
}