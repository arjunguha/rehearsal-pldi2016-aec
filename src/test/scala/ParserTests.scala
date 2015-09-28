import rehearsal._
import Parser._
import Syntax._

class ParserTestSuite extends org.scalatest.FunSuite {

	test("constant"){
		val bool1 = "true"
		val bool2 = "false"
		val str1 = "\"hello\""
		val str2 = "'hello'"
		assert(parseBool(bool1) == Bool(true))
		assert(parseBool(bool2) == Bool(false))
		assert(parseStr(str1) == Str("hello"))
		assert(parseStr(str2) == Str("hello"))
	}

	test("op1"){
		val not = "!true"
		assert(parseOps(not) == Not(Bool(true)))
	}

	test("op2"){
		val and = "true and true"
		val and2 = "true and true and false"
		val or = "true or false"
		val eq = "'hi' == 'hi'"
		val neq = "'hi' != 'hello'"
		val mat = "'hi' =~ '[a-z]*'"
		val nmat = "'hi' !~ '[a]*'"
		val in = "'h' in 'hello'"
		assert(parseOps(and) == And(Bool(true), Bool(true)))
		assert(parseOps(and2) == And(And(Bool(true), Bool(true)), Bool(false)))
		assert(parseOps(or) == Or(Bool(true), Bool(false)))
		assert(parseOps(eq) == Eq(Str("hi"), Str("hi")))
		assert(parseOps(neq) == Not(Eq(Str("hi"), Str("hello"))))
		assert(parseOps(mat) == Match(Str("hi"), Str("[a-z]*")))
		assert(parseOps(nmat) == Not(Match(Str("hi"), Str("[a]*"))))
		assert(parseOps(in) == In(Str("h"), Str("hello")))
	}

	test("expr"){
		val resourceRef = "file['/bin']"
		val vari = "$x"
		assert(parseExpr(resourceRef) == Res("file", Str("/bin")))
		assert(parseExpr(vari) == Var("x"))
	}

	test("Attribute"){
		val attr1 = "ensure => 'present'"
		val attr2 = "ensure => present"
		val attr3 = "content => true"
		val attr4 = "require => File['/home']"
		val attr5 = "require => $x"
		val attr6 = "content => true and false"
		assert(parseAttribute(attr1) == Attribute(Str("ensure"), Str("present")))
		assert(parseAttribute(attr2) == Attribute(Str("ensure"), Str("present")))
		assert(parseAttribute(attr3) == Attribute(Str("content"), Bool(true)))
		assert(parseAttribute(attr4) == Attribute(Str("require"), Res("File", Str("/home"))))
		assert(parseAttribute(attr5) == Attribute(Str("require"), Var("x")))
		assert(parseAttribute(attr6) == Attribute(Str("content"), And(Bool(true), Bool(false))))
	}

	test("Argument"){
		val arg1 = "String $x = 'hello'"
		val arg2 = "String $x"
		val arg3 = "$x = 'hello'"
		assert(parseArgument(arg1) == Argument("x", Some(Str("hello"))))
		assert(parseArgument(arg2) == Argument("x", None))
		assert(parseArgument(arg3) == Argument("x", Some(Str("hello"))))
	}

	test("resource"){
		val prog = "user { 'awe': ensure => present }"
		val res = Resource(Str("awe"), "user", Seq(Attribute(Str("ensure"), Str("present"))))
		assert(parseManifest(prog) == res)
	}

	test("ite"){
		val prog = """
			if true {
				user { 'awe': ensure => present }
			}
		"""
		assert(parseManifest(prog) == ITE(Bool(true),
			Resource(Str("awe"), "user", Seq(Attribute(Str("ensure"), Str("present")))), Empty))
	}

	test("edge"){
		val edge1 = "user { 'awe': ensure => 'present' } -> file { '/home': ensure => present }"
		val edge2 = "user { 'awe': ensure => 'present' } <- file { '/home': ensure => present } "
		assert(parseManifest(edge1) ==
			Edge(Resource(Str("awe"), "user", Seq(Attribute(Str("ensure"), Str("present")))),
					 Resource(Str("/home"), "file", Seq(Attribute(Str("ensure"), Str("present"))))))
		assert(parseManifest(edge2) ==
			Edge(Resource(Str("/home"), "file", Seq(Attribute(Str("ensure"), Str("present")))),
					 Resource(Str("awe"), "user", Seq(Attribute(Str("ensure"), Str("present"))))))
	}

	test("define"){
		val expr = """
			define foo($bar = 'baz') {
				file { 'foo':
					ensure => 'present',
				}
			}
		"""
		val res = Define("foo",
								Seq(Argument("bar", Some(Str("baz")))),
								Resource(Str("foo"), "file", Seq(Attribute(Str("ensure"), Str("present"))))
							)
		assert(parseManifest(expr) == res)
	}

	test("let"){
		val prog = """
			$x = 'hi!'
			file { $x: ensure => 'present' }
		"""
		val res = Let("x", Str("hi!"), Resource(Var("x"), "file", Seq(Attribute(Str("ensure"), Str("present")))))
		assert(parseManifest(prog) == res)
	}

	test("block"){
		val prog = """
			define foo($bar = 'baz') {
				file { 'foo':
					ensure => 'present',
				}
			}
			user { 'awe':
				ensure => 'present',
				foo => 'bar'
			}
			file { '/foo':
				ensure => 'present',
				foo => 'bar'
			}
		"""
		val res = Block(Define("foo",	Seq(Argument("bar", Some(Str("baz")))),
								Resource(Str("foo"), "file", Seq(Attribute(Str("ensure"), Str("present"))))
							), Block(
					Resource(Str("awe"), "user", Seq(Attribute(Str("ensure"), Str("present")),
																							 Attribute(Str("foo"), Str("bar")))),
					Resource(Str("/foo"), "file", Seq(Attribute(Str("ensure"), Str("present")),
																							 Attribute(Str("foo"), Str("bar")))))
		)
		assert(parse(prog) == res)
	}

	test("E"){
		val resourceRef = "file['/bin']"
		val vari = "$x"
		assert(parse(resourceRef) == E(Res("file", Str("/bin"))))
		assert(parse(vari) == E(Var("x")))
	}
}