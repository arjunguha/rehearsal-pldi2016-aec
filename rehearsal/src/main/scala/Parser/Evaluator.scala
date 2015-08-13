package eval

import parser.Internal._

object Eval {

	case class EvalError(msg: String) extends RuntimeException(msg)

	def subPred(id: String, value: Atom, pred: BoolOps): BoolOps = pred match {
		case BAtom(AVar(i)) if i == id => BAtom(value)
		case BAnd(lhs, rhs) => BAnd(subPred(id, value, lhs), subPred(id, value, rhs))
		case BOr(lhs, rhs) => BOr(subPred(id, value, lhs), subPred(id, value, rhs))
		case BNot(arg) => BNot(subPred(id, value, arg))
		case BEq(lhs, rhs) => BEq(subPred(id, value, lhs), subPred(id, value, rhs))
		case BNEq(lhs, rhs) => BNEq(subPred(id, value, lhs), subPred(id, value, rhs))
		case BMatch(lhs, rhs) => BMatch(subPred(id, value, lhs), subPred(id, value, rhs))
		case BNMatch(lhs, rhs) => BNMatch(subPred(id, value, lhs), subPred(id, value, rhs))
		case BIn(lhs, rhs) => BIn(subPred(id, value, lhs), subPred(id, value, rhs))
	}	

	def subArgs(id: String, value: Atom, args: Seq[Argument]): Seq[Argument] = 
		args.foldRight[Seq[Argument]](Seq()){
			case (Argument(n, t, Some(AVar(v))), acc) if v == id => Argument(n, t, Some(value)) +: acc
			case (arg, acc) => arg +: acc
		}

	def subAttrs(id: String, value: Atom, attrs: Seq[Attribute]) = 
		attrs.foldRight[Seq[Attribute]](Seq()){
			case (Attribute(n, AVar(v)), acc) if v == id => Attribute(n, value) +: acc
			case (attr, acc) => attr +: acc
		}
	
	def sub(id: String, value: Atom, mani: Manifest): Manifest = mani match {
		case Resource(AVar(x), typ, attrs) if x == id => Resource(value, typ, subAttrs(id, value, attrs))
		case Resource(name, typ, attrs) => Resource(name, typ, subAttrs(id, value, attrs))
		case Block(e1, e2) => Block(sub(id, value, e1), sub(id, value, e2))
		case Let(i, AVar(x), body) if x == id => Let(i, value, sub(id, value, body))
		case Let(i, v, body) => Let(i, v, sub(id, value, body))
		case Define(name, args, body) => Define(name, subArgs(id, value, args), sub(id, value, body))
		case ITE(pred, e1, e2) => ITE(subPred(id, value, pred), sub(id, value, e1), sub(id, value, e2))
		case Class(name, params, body) => Class(name, subArgs(id, value, params), sub(id, value, body))
		case _ => mani
	}	

	def evalPred(pred: BoolOps): Boolean = pred match {
		case BAtom(ABool(b)) => b
		case BAnd(lhs, rhs) => evalPred(lhs) && evalPred(rhs)
		case BOr(lhs, rhs) => evalPred(lhs) || evalPred(rhs)
		case BNot(arg) => !evalPred(arg)
		case BEq(BAtom(AString(a)), BAtom(AString(b))) => a == b
		case BEq(a, b) => evalPred(a) == evalPred(b)
		case BNEq(BAtom(AString(a)), BAtom(AString(b))) => a != b
		case BNEq(a, b) => evalPred(a) != evalPred(b)
		case BMatch(BAtom(AString(lhs)), BAtom(AString(rhs))) => {
			val pat = rhs.r
			lhs match {
				case pat(_) => true
				case _ => false
			}
		}
		case BNMatch(BAtom(AString(lhs)), BAtom(AString(rhs))) => {
			val pat = rhs.r
			lhs match {
				case pat(_) => false
				case _ => true
			}
		}
		case BIn(BAtom(AString(lhs)), BAtom(AString(rhs))) => rhs.contains(lhs)
		case _ => throw EvalError(s"Cannot evaluate: invalid predicate: $pred")
	}

	def eval(mani: Manifest): Manifest = mani match {
		case EmptyExpr => mani
		case Block(e1, e2) => Block(eval(e1), eval(e2))
		case Resource(_, _, _) => mani
		case Edge(_, _) => mani
		case Let(id, value, body) => sub(id, value, body)
		case Define(name, args, body) => Define(name, args, eval(body))
		case ITE(pred, thn, els) => if(evalPred(pred)) eval(thn) else eval(els)
		case Class(name, args, body) => Class(name, args, eval(body))
	}
	
	
}