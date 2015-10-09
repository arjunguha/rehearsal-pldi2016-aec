class SimpleEvalTests extends org.scalatest.FunSuite {

	import rehearsal._
	import PuppetParser2._
	import PuppetSyntax2._
	import PuppetEval2._
	import java.nio.file._
	import scala.collection.JavaConversions._
  import scalax.collection.Graph
  import scalax.collection.Graph._
  import scalax.collection.GraphPredef._
  import scalax.collection.GraphEdge._
  import scalax.collection.edge.Implicits._

	for (path <- Files.newDirectoryStream(Paths.get("parser-tests/good"))) {

		test(path.toString) {
			parseFile(path.toString)
			val EvaluatedManifest(resources, deps) = eval(parseFile(path.toString))
			if (deps.nodes.length == 0) {
				info("No resources found -- a trivial test")
			}
			for (node <- deps.nodes) {
				assert(primTypes.contains(node.value.typ), s"${node.value.typ} not elaborated")
			}
		}

	}

	test("simple before relationship") {

		val EvaluatedManifest(r, g) = eval(parse("""
      file{"A":
        before => File["B"]
      }
      file{"B": }
    """))

    assert(r.size == 2)
    assert(g == Graph(Node("file", "A") ~> Node("file", "B")))

	}

	test("require relationship with an array") {

		val EvaluatedManifest(r, g) = eval(parse("""
      file{"A":
        require => [File["B"], File["C"]]
      }
      file{"B": }
      file{"C": }
    """))

    assert(r.size == 3)
    assert(g == Graph(Node("file", "B") ~> Node("file", "A"),
                      Node("file", "C") ~> Node("file", "A")))
	}

	test("eval-expandAll 1") {
		val prog = """
			define fun($a, $b){
				foo { '/home':
					require => $a,
					before => $b
				}
			}
			fun {'instance':
				a => File["A"],
				b => File["B"]
			}
			file{"A": }
			file{"B": }"""
		val EvaluatedManifest(r, g) = parse(prog).eval()
		assert(r.size == 3)
		assert(g == Graph(Node("file", "A") ~> Node("foo", "/home"),
		                 Node("foo", "/home") ~> Node("file", "B")))
	}

  test("expandAll: 2 defines") {
    val prog = """
			define funOne($a, $b){
				foo { "1":
					require => $a,
					before => $b
				}
			}
			define funTwo($a){
				bar { "2": attr => $a }
			}
			funOne { "i1":
				a => File["apple"],
				b => File["banana"]
			}
			funTwo { "i2": a => "A" }
			file { "apple": }
			file { "banana": }"""
    val EvaluatedManifest(r, g) = parse(prog).eval()
    assert(r.size == 4)
    assert(g == Graph(Node("file", "apple") ~> Node("foo", "1"),
                      Node("foo", "1") ~> Node("file", "banana"),
                      Node("bar", "2")))
  }

  test("expandAll - 2 instances") {
    val prog = """
			f { "instance":
				a => "one",
				b => "two",
				c => true
			}
			define f($a, $b, $c){
				if $c {
					file { "1": content => $a }
				}else{
					file { "2": content => $b }
				}
			}
			f { "instance2":
				a => "purple",
				b => "yellow",
				c => false
			}"""
    val EvaluatedManifest(r, g) = parse(prog).eval()
    assert(r.size == 2)
    assert(g == Graph(Node("file", "1"), Node("file", "2")))
  }

  test("expandAll - instance in define") {
    val prog = """
			define f($a, $b, $c){
				if $c {
					file { "1": content => $a }
				}else{
					file { "2": content => $b }
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
				pred => true
			}"""
    val EvaluatedManifest(r, g) = parse(prog).eval()
    assert(r.size == 1)
    assert(g == Graph(Node("file", "1")))
  }

  test("edges with arrays") {
    val prog = """
			file { "/usr/rian/foo": }
			file { "/usr/rian/bar": }
			file { "/": }
			file { "/usr/": }
			file { "/usr/rian/":
				before => [File["/usr/rian/foo"], File["/usr/rian/bar"]],
				require => [File["/"], File["/usr/"]]
			}"""
    val EvaluatedManifest(r, g) = parse(prog).eval()
    assert(r.size == 5)
    assert(g == Graph(Node("file", "/usr/rian/") ~> Node("file", "/usr/rian/foo"),
                      Node("file", "/usr/rian/") ~> Node("file", "/usr/rian/bar"),
                      Node("file", "/") ~> Node("file", "/usr/rian/"),
                      Node("file", "/usr/") ~> Node("file", "/usr/rian/")))
  }

  test("eval-expandAll: no arguments") {
    val prog = """
			define fun(){
				hello { "foo": a => "b" }
			}
			fun { 'i': }"""
    val EvaluatedManifest(r, g) = parse(prog).eval()
    assert(r.size == 1)
    assert(g == Graph(Node("hello", "foo")))
  }

  test("edges with singleton arrays") {
    val prog = """
			file { "/usr/rian/foo": }
			file { "/": }
			file { "/usr/rian/":
				before => [File["/usr/rian/foo"]],
				require => [File["/"]]
			}"""
    val EvaluatedManifest(r, g) = parse(prog).eval()
    assert(r.size == 3)
    assert(g == Graph(Node("file", "/usr/rian/") ~> Node("file", "/usr/rian/foo"),
                      Node("file", "/") ~> Node("file", "/usr/rian/")))
  }

}