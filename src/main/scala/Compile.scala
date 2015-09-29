package rehearsal

object Compile {

	import java.nio.file.{Path, Paths}
	import rehearsal.{FSSyntax => F}
	import FSSyntax.{True, False, Expr, Not, Or, Block, Skip}
	import rehearsal.Implicits._
	import rehearsal.{Syntax => P}
	import Syntax._

	case class FSCompileError(msg: String) extends RuntimeException(msg)

	//Must evaluate before compiling??


	//TODO: make this work
	//PROBLEM: some of these should compile to Pred, others to F.Expr

	// def compileExpr(e: P.Expr): F.Expr = e match {
	// 	case Str(s) => throw FSCompileError("NYI") //??
	// 	case Res(typ, e) => throw FSCompileError("NYI") //??
	// 	case Bool(true) => True
	// 	case Bool(false) => False
	// 	case P.Not(e) => F.Not(compileExpr(e))
	// 	case P.And(e1, e2) => F.Not(compileExpr(e1), compileExpr(e2))
	// 	case P.Or(e1, e2) => F.Or(compileExpr(e1), compileExpr(e2))
	// 	case Eq(e1, e2) => throw FSCompileError("NYI") //??
	// 	case Match(e1, e2) => throw FSCompileError("NYI") //??
	// 	case In(e1, e2) => throw FSCompileError("NYI") //??
	// 	case Array(_) => throw FSCompileError("NYI") //??

	// 	case Var(_) => throw FSCompileError("Var: not a value")
	// 	case App(_, _) => throw FSCompileError("App: not a value")
	// }

	//TODO: fill this in
	def compileResource(title: P.Expr, typ: String, attrs: Seq[Attribute]) = Skip

	def compile(m: Manifest): F.Expr = m match {
		case Empty => Skip
		case P.Block(m1, m2) => F.Block(compile(m1), compile(m2))
		case Resource(title, typ, attrs) => compileResource(title, typ, attrs)
		case Edge(m1, m2) => Skip //TODO: figure out what to do with edges
		//TODO: fix this
		case E(e) => throw FSCompileError("NYI") //compileExpr(e)
		case P.ITE(_, _, _) => throw FSCompileError("ITE: not a value")	//may not need this to be a value
		case Define(name, params, body) => throw FSCompileError("Define: not a value")
		case Class(name, params, inherits, body) => throw FSCompileError("Class: should have been desugared")
		case Let(varName, e, body) => throw FSCompileError("Let: not a value")
		case MCase(e, cases) => throw FSCompileError("Case statement: should have been desugared")
	}

}
