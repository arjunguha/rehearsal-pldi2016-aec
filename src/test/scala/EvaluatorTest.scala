import rehearsal._
import Parser._
import Syntax._
import Evaluator._
import scalax.collection.mutable.Graph
import scalax.collection.mutable.Graph._
import scalax.collection.GraphEdge._


class EvaluatorTestSuite extends org.scalatest.FunSuite {

	test("test1"){
		val prog = Let("x", Bool(true),
								E(ITE(Not(Var("x")), E(Str("oops")),
									E(And(Var("x"), Or(Var("x"), Not(Var("x"))))))))
		val res = E(Bool(true))
		assert(eval(prog) == res)
	}

	test("test2"){
		assert(eval(E(Not(Bool(true)))) == E(Bool(false)))
		assert(eval(E(Not(Bool(false)))) == E(Bool(true)))
		assert(eval(E(And(Bool(true), Bool(true)))) == E(Bool(true)))
		assert(eval(E(And(Bool(true), Bool(false)))) == E(Bool(false)))
		assert(eval(E(And(Bool(false), Bool(true)))) == E(Bool(false)))
		assert(eval(E(And(Bool(false), Bool(false)))) == E(Bool(false)))
		assert(eval(E(Or(Bool(true), Bool(true)))) == E(Bool(true)))
		assert(eval(E(Or(Bool(true), Bool(false)))) == E(Bool(true)))
		assert(eval(E(Or(Bool(false), Bool(true)))) == E(Bool(true)))
		assert(eval(E(Or(Bool(false), Bool(false)))) == E(Bool(false)))
	}

	test("graphEmpty"){
		assert(toGraph(Empty) == Graph())
	}

	test("graph empty block"){
		assert(toGraph(Block(Empty, Empty)) == Graph())
	}

	test("graph resource"){
		assert(toGraph(Resource(Str("1"), "typ", Seq(Attribute(Str("ensure"), Str("present")))))
			== Graph(Resource(Str("1"), "typ", Seq(Attribute(Str("ensure"), Str("present"))))))
	}

	test("graph edge"){
		assert(toGraph(Edge(Resource(Str("1"), "1", Seq()), Resource(Str("2"), "2", Seq()))) ==
			Graph(Resource(Str("1"), "1", Seq()), Resource(Str("2"), "2", Seq()),
						DiEdge(Resource(Str("1"), "1", Seq()), Resource(Str("2"), "2", Seq()))))
	}

	test("graph block"){
		assert(toGraph(Block(Resource(Str("1"), "1", Seq()), Resource(Str("2"), "2", Seq()))) ==
			Graph(Resource(Str("1"), "1", Seq()), Resource(Str("2"), "2", Seq())))
	}

}
