package parser

import Syntax2._

object Evaluator2 {

	def sub(varName: String, e: Expr, body: Manifest): Manifest = Empty

	//a.name -> Str; a.value -> Constant|Res
	// def evalAttr(a: Attribute): Attribute = a match {
	// 	// case Attribute(Res(_, _), v) => //doesn't make sense
	// 	// case Attribute(Var(name), v) => Attribute(sub(name), v)
	// 	// case Attribute(Str(_), _) => a
	// 	// case Attribute(Bool(_), _) => //doesn't make sense
	// 	case Attribute(op@Bool(_), v) => Attribute(evalBool(op), v)
	// 	case Attribute(Expr, _) => a
	// 	case _ => a
	// }
	
	/*eval :: m => m'
		m' ::= m1';m2'
					| typ{a1'...an'}
					| m1' -> m2'
					| typ1[str1] -> typ2[str2]
					| define f(x1...xn){m}
	*/
	def eval(m: Manifest): Manifest = m match {
		case Empty => Empty
		case Block(m1, m2) => Block(eval(m1), eval(m2))
		case Resource(typ, attrs) => 
		case ITE(pred, m1, m2) => if(eval(pred) == Bool(true)) eval(m1) else eval(m2)
		case Edge(m1, m2) => Edge(eval(m1), eval(m2))
		case Define(_, _, _) => m
		case Let(varName, e, body) => sub(varName, e, body)
		case Res(typ, e) => Res(typ, eval(e))
		case Var(_) => m
		case Str(_) => m
		case Bool(_) => m
		case Not(e) => match eval(e){
			case Bool(b) => Bool(!b)
			case _ => m //can't evaluate further
		}
		case And(e1, e2) => match (eval(e1), eval(e2)) {
			case (Bool(b1), Bool(b2)) => Bool(b1 && b2)
			case _ => m //can't evaluate further
		case Or(e1, e2) => match (eval(e1), eval(e2)) {
			case (Bool(b1), Bool(b2)) => Bool(b1 || b2)
			case _ => m //can't evaluate further
		case Eq(e1, e2) => eval(e1) == eval(e2)
		case Match(e2, e2) => 
		case In(e1, e2) =>
	}
	
}