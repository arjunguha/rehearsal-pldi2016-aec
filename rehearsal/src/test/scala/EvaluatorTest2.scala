import parser.Parser2._
import parser.Syntax2._
import parser.Evaluator2._
import scalax.collection.mutable.Graph
import scalax.collection.mutable.Graph._
import scalax.collection.GraphEdge._


class EvaluatorTestSuite2 extends org.scalatest.FunSuite {

	test("test1"){
		val prog = Let("x", Bool(true), 
								ITE(Not(Var("x")), E(Str("oops")),
									E(And(Var("x"), Or(Var("x"), Not(Var("x")))))))
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
		assert(toGraph(Graph(), Empty) == Graph())
	}

	test("graph empty block"){
		assert(toGraph(Graph(), Block(Empty, Empty)) == Graph())
	}

	test("graph resource"){
		assert(toGraph(Graph(), Resource("typ", Seq(Attribute(Str("ensure"), Str("present"))))) == 
			Graph(Resource("typ", Seq(Attribute(Str("ensure"), Str("present"))))))
	}

	test("graph edge"){
		assert(toGraph(Graph(), Edge(Resource("1", Seq()), Resource("2", Seq()))) == 
			Graph(Resource("1", Seq()), Resource("2", Seq()), 
						DiEdge(Resource("1", Seq()), Resource("2", Seq()))))
	}

	test("graph block"){
		assert(toGraph(Graph(), Block(Resource("1", Seq()), Resource("2", Seq()))) == 
			Graph(Resource("1", Seq()), Resource("2", Seq())))
	}

	test("expand: no arguments"){
		val d = Define("fun", Seq(), Resource("hello", Seq(Attribute(Str("a"), Str("b")))))
		val i = Resource("fun", Seq())
		assert(expand(i, d) == Resource("hello", Seq(Attribute(Str("a"), Str("b")))))
	}

	test("expand"){
		val d = Define("fun", Seq(Argument("a"), Argument("b")), 
										Resource("foo", Seq(Attribute(Str("requires"), Var("a")), 
																				Attribute(Str("before"), Var("b")))))
		val i = Resource("fun", Seq(Attribute(Str("a"), Str("A")), Attribute(Str("b"), Str("B"))))
		assert(expand(i, d) == Resource("foo", Seq(Attribute(Str("requires"), Str("A")), 
																							 Attribute(Str("before"), Str("B")))))
	}

	test("expandAll"){
		val d1 = Define("fun1", Seq(Argument("a"), Argument("b")), 
										Resource("foo", Seq(Attribute(Str("requires"), Var("a")), 
																				Attribute(Str("before"), Var("b")))))
		val d2 = Define("fun2", Seq(Argument("a"), Argument("b")), 
										Resource("foo", Seq(Attribute(Str("requires"), Var("a")), 
																				Attribute(Str("before"), Var("b")))))
		val i1 = Resource("fun1", Seq(Attribute(Str("a"), Str("apple")), Attribute(Str("b"), Str("banana"))))
		val i2 = Resource("fun2", Seq(Attribute(Str("a"), Str("A")), Attribute(Str("b"), Str("B"))))
		val prog = Block(d1, Block(d2, Block(i1, i2)))
		val res = Block(Resource("foo", Seq(Attribute(Str("requires"), Str("apple")), 
																				Attribute(Str("before"), Str("banana")))),
										Resource("foo", Seq(Attribute(Str("requires"), Str("A")), 
																				Attribute(Str("before"), Str("B")))))
		assert(eval(expandAll(eval(prog))) == res)
	}

	test("eval-expandAll"){
		val prog = """
			define f($a, $b, $c){
				if $c {
					file { "1": "content" => $a }
				}else{
					file { "2": "content" => $b }
				}
			}

			f { "instance": 
				$a => "one",
				$b => "two",
				$c => true
			}
		"""
		val res = Resource("file", Seq(Attribute(Str("content"), Str("one"))))
		assert(eval(expandAll(parse(prog))) == res)
	}
}