import parser.Parser._
import parser.Syntax._
import parser.Evaluator._
import scalax.collection.mutable.Graph
import scalax.collection.mutable.Graph._
import scalax.collection.GraphEdge._


class EvaluatorTestSuite extends org.scalatest.FunSuite {

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

	test("eval-expandAll: no arguments"){
		val prog = """
			define fun(){
				hello { "foo": "a" => "b" }
			}
			fun { 'i': }
		"""
		val res = "hello {'foo': 'a' => 'b' }"
		assert(toGraph(eval(expandAll(parse(prog)))) == toGraph(parse(res)))
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
		val res = """
			foo { '/home': }
			'A' -> Foo['/home']
			'B' <- Foo['/home']
		"""
		assert(toGraph(eval(expandAll(parse(prog)))) == toGraph(parse(res)))
	}

	test("expandAll: 2 defines"){
		val prog = """
			define funOne($a, $b){
				foo { "1": 
					require => $a,
					before => $b
				}
			}
			define funTwo($a){
				bar { "2": "attr" => $a }
			}
			funOne { "i1": 
				a => "apple",
				b => "banana"
			}
			funTwo { "i2": a => "A" }
		"""

		val res = """
			foo { "1": }
			"apple" -> Foo["1"]
			Foo["1"] -> "banana"
			bar { "2": "attr" => "A" }
		"""
		assert(toGraph(eval(expandAll(eval(parse(prog))))) == toGraph(parse(res)))
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
		val evald = eval(expandAll(parse(prog)))
		val res = Resource(Str("1"), "file", Seq(Attribute(Str("content"), Str("one"))))
		assert(evald == res)
		assert(toGraph(evald) == toGraph(res))
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
		val evald = eval(expandAll(parse(prog)))
		val res = Block(Resource(Str("1"), "file", Seq(Attribute(Str("content"), Str("one")))), 
										Resource(Str("2"), "file", Seq(Attribute(Str("content"), Str("yellow")))))
		assert(evald == res)
		assert(toGraph(evald) == 
			Graph(Resource(Str("1"), "file", Seq(Attribute(Str("content"), Str("one")))),
						Resource(Str("2"), "file", Seq(Attribute(Str("content"), Str("yellow"))))))
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
		val evald = eval(expandAll(parse(prog)))
		val res = "file { '1': 'content' => 'purple' }"
		assert(evald == parse(res))
		assert(toGraph(evald) == toGraph(parse(res)))
	}

}