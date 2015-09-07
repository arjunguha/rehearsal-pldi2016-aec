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
		assert(toGraph(Graph(), Resource(Str("1"), "typ", Seq(Attribute(Str("ensure"), Str("present"))))) == 
			Graph(Resource(Str("1"), "typ", Seq(Attribute(Str("ensure"), Str("present"))))))
	}

	test("graph edge"){
		assert(toGraph(Graph(), Edge(Resource(Str("1"), "1", Seq()), Resource(Str("2"), "2", Seq()))) == 
			Graph(Resource(Str("1"), "1", Seq()), Resource(Str("2"), "2", Seq()), 
						DiEdge(Resource(Str("1"), "1", Seq()), Resource(Str("2"), "2", Seq()))))
	}

	test("graph block"){
		assert(toGraph(Graph(), Block(Resource(Str("1"), "1", Seq()), Resource(Str("2"), "2", Seq()))) == 
			Graph(Resource(Str("1"), "1", Seq()), Resource(Str("2"), "2", Seq())))
	}

	test("eval-expandAll: no arguments"){
		val prog = """
			define fun(){
				hello { "foo": "a" => "b" }
			}
			fun { 'i': }
		"""
		assert(eval(expandAll(parse(prog))) == Resource(Str("foo"), "hello", Seq(Attribute(Str("a"), Str("b")))))
	}

	test("eval-expandAll 1"){
		val prog = """
			define fun($a, $b){
				foo { '/home': 
					"require" => $a,
					"before" => $b
				}
			}
			fun {'instance': 
				a => "A",
				b => "B"
			}
		"""
		assert(eval(expandAll(parse(prog))) == Block(Resource(Str("/home"),"foo",List()),
																								 Block(Edge(E(Str("A")),E(Res("Foo",Str("/home")))),
																								 			 Edge(E(Res("Foo",Str("/home"))),E(Str("B"))))))
	}

	test("expandAll: 2 defines"){
		val d1 = Define("fun1", Seq(Argument("a"), Argument("b")), 
										Resource(Str("1"), "foo", Seq(Attribute(Str("require"), Var("a")), 
																				Attribute(Str("before"), Var("b")))))
		val d2 = Define("fun2", Seq(Argument("a"), Argument("b")), 
										Resource(Str("2"), "foo", Seq(Attribute(Str("require"), Var("a")), 
																				Attribute(Str("before"), Var("b")))))
		val i1 = Resource(Str("i1"), "fun1", Seq(Attribute(Str("a"), Str("apple")), Attribute(Str("b"), Str("banana"))))
		val i2 = Resource(Str("i2"), "fun2", Seq(Attribute(Str("a"), Str("A")), Attribute(Str("b"), Str("B"))))
		val prog = Block(d1, Block(d2, Block(i1, i2)))
		val res = Block(Resource(Str("1"), "foo", Seq(Attribute(Str("require"), Str("apple")), 
																				Attribute(Str("before"), Str("banana")))),
										Resource(Str("2"), "foo", Seq(Attribute(Str("require"), Str("A")), 
																				Attribute(Str("before"), Str("B")))))
		assert(eval(expandAll(eval(prog))) == res)
	}

	test("eval-expandAll2"){
		val prog = """
			define f($a, $b, $c){
				if $c {
					file { "1": "content" => $a }
				}else{
					file { "2": "content" => $b }
				}
			}

			f { "instance": 
				a => "one",
				b => "two",
				c => true
			}
		"""
		val res = Resource(Str("1"), "file", Seq(Attribute(Str("content"), Str("one"))))
		assert(eval(expandAll(parse(prog))) == res)
	}

	test("expandAll - 2 instances"){
		val prog = """
			f { "instance": 
				a => "one",
				b => "two",
				c => true
			}
			define f($a, $b, $c){
				if $c {
					file { "1": "content" => $a }
				}else{
					file { "2": "content" => $b }
				}
			}
			f { "instance2": 
				a => "purple",
				b => "yellow",
				c => false
			}
		"""
		val res = Block(Resource(Str("1"), "file", Seq(Attribute(Str("content"), Str("one")))), 
										Resource(Str("2"), "file", Seq(Attribute(Str("content"), Str("yellow")))))
		assert(eval(expandAll(parse(prog))) == res)
	}

	test("expandAll - instance in define"){
		val prog = """
			define f($a, $b, $c){
				if $c {
					file { "1": "content" => $a }
				}else{
					file { "2": "content" => $b }
				}
			}
			define g($pred){
				f { "instance1": 
					a => "purple",
					b => "yellow",
					c => $pred
				}
			}
			g { "instance2":
				$pred => true
			}
		"""
		val res = "file { '1': 'content' => 'purple' }"
		assert(eval(expandAll(parse(prog))) == parse(res))
	}

}