import eval.Eval._
import parser.Internal._
import parser.Parser._
import parser.Syntax.{convertBoolOps, convert}


class EvaluatorTestSuite extends org.scalatest.FunSuite {
	test("subpred"){
		assert(subPred("x", ABool(true), BAtom(AVar("x"))) == BAtom(ABool(true)))
		assert(subPred("x", ABool(true), BAnd(BAtom(AVar("x")), BAtom(AVar("x")))) == 
			BAnd(BAtom((ABool(true))), BAtom(ABool(true))))
		assert(subPred("x", ABool(true), BOr(BAtom(AVar("x")), BAtom(AVar("x")))) == 
			BOr(BAtom((ABool(true))), BAtom(ABool(true))))
		assert(subPred("x", ABool(true), BNot(BAtom(AVar("x")))) == 
			BNot(BAtom(ABool(true))))
		assert(subPred("x", ABool(true), BEq(BAtom(AVar("x")), BAtom(AVar("x")))) == 
			BEq(BAtom((ABool(true))), BAtom(ABool(true))))
		assert(subPred("x", ABool(true), BNEq(BAtom(AVar("x")), BAtom(AVar("x")))) == 
			BNEq(BAtom((ABool(true))), BAtom(ABool(true))))
		assert(subPred("x", ABool(true), BMatch(BAtom(AVar("x")), BAtom(AVar("x")))) == 
			BMatch(BAtom((ABool(true))), BAtom(ABool(true))))
		assert(subPred("x", ABool(true), BNMatch(BAtom(AVar("x")), BAtom(AVar("x")))) == 
			BNMatch(BAtom((ABool(true))), BAtom(ABool(true))))
		assert(subPred("x", ABool(true), BIn(BAtom(AVar("x")), BAtom(AVar("x")))) == 
			BIn(BAtom((ABool(true))), BAtom(ABool(true))))
	}

	test("subargs"){
		assert(subArgs("x", ABool(true), Seq(Argument("hi", "file", Some(AVar("x"))))) == 
			Seq(Argument("hi", "file", Some(ABool(true)))))
	}

	test("sub"){
		assert(sub("x", ABool(true), Resource(AString("foo"), "file", Seq(Attribute("ensure", AVar("x")))))
			== Resource(AString("foo"), "file", Seq(Attribute("ensure", ABool(true)))))
		assert(sub("x", AString("foo"), Resource(AVar("x"), "file", Seq(Attribute("ensure", ABool(true)))))
			== Resource(AString("foo"), "file", Seq(Attribute("ensure", ABool(true)))))
	}

	test("evalPred"){
		val prog = """
			'/foo/foo' =~ '(/foo)*'
		"""
		assert(evalPred(convertBoolOps(parseBoolOps(prog))))
		val prog2 = """
			'/foo' in '/foo/bar'
		"""
		assert(evalPred(convertBoolOps(parseBoolOps(prog2))))
	}

	test("eval"){
		val prog = """
			if true{
				file { 'foo': ensure => present }
			}else {
				file { 'bar': ensure => absent }
			}
		"""
		assert(eval(desugar(convert(parse(prog)))) == 
			Resource(AString("foo"), "file", Seq(Attribute("ensure", ASymbol("present")))))
	}
}