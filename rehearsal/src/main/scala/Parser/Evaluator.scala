package eval

import parser.Internal._
import scalax.collection.mutable.Graph
import scalax.collection.mutable.Graph._
import scalax.collection.GraphEdge._

object Eval {

	case class EvalError(msg: String) extends RuntimeException(msg)

	type ManifestGraph = Graph[Manifest, DiEdge]
	sealed trait Direction
	case object Left extends Direction
	case object Right extends Direction
	case object NoDep extends Direction

	//ToDo: INCOMPLETE: must look at args, attrs, & pred
	def isIn(name: String, e: Manifest): Boolean = e match {
		case EmptyExpr => false
		case Block(e1, e2) => isIn(name, e1) || isIn(name, e2)
		case Resource(id, _, _) if id == name => true
		case Resource(_, _, _) => false
		case Edge(e1, e2) if e1 == name || e2 == name => true
		case Edge(_, _) => false
		case Let(_, _, body) => isIn(name, body)
		case App(id, _) if id == name => true
		case Define(n, _, _) if n == name => true
		case Define(_, _, body) => isIn(name, body)
		case ITE(_, thn, els) => isIn(name, thn) || isIn(name, els)
		case Class(n, _, _) if n == name => true
		case Class(_, _, body) => isIn(name, body)
	}

	/* if e2 depends on e1: return true
	 * o.w. false
	 */
	def depends(e1: Manifest, e2: Manifest): Boolean = e1 match {
		case EmptyExpr => false
		case Resource(_, _, _) => false
		case Edge(_, _) => false
		case Let(_, _, _) => false
		case App(_, _) => false
		case Define(name, args, body) if isIn(name, e2) => true
		case Define(_, _, _) => false
		case ITE(_, _, _) => false
		case Class(name, args, body) if isIn(name, e2) => true
		case Block(e11, e12) => depends(e11, e2) || depends(e12, e2)
	}
	
	/* Sketch

	e1 match {
		case EmptyExpr => NoDep
		case Resource => NoDep
		case Edge => NoDep
		case Let => NoDep
		case App => NoDep
		case Define(n, a, b) if n IN e2 => Left
		case Define => NoDep
		case ITE => NoDep
		case Class(n, a, b) if n IN e2 => Left
		case Class => NoDep
		case Block(e11, e12) => depends(e11, e2) == Left || depends(e12, e2) == Left => Left
	}

	 */
	 //TODO: fix and uncomment if statement
	def manifestToGraph(m: Manifest): ManifestGraph = m match {
		case EmptyExpr => Graph()
		case Resource(_, _, _) => Graph(m)
		case Edge(_, _) => Graph(m)
		case App(_, _) => Graph(m)
		case Let(_, _, _) => Graph(m)
		case Define(_, _, _) => Graph(m)
		case ITE(_, _, _) => Graph(m)
		case Class(_, _, _) => Graph(m)
		case Block(e1, e2) => {
			val (g1, g2) = (manifestToGraph(e1), manifestToGraph(e2))
			val g3: ManifestGraph = g1 ++ g2
			//if(depends(e1, e2)) g3 += e1 ~> e2 else if(depends(e2, e1)) g3 += e2 ~> e1
			g3
		}
	}

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
                case Edge(AVar(x), AVar(y)) if x == id && y == id => Edge(value, value)
                case Edge(AVar(x), child) if x == id => Edge(value, child)
                case Edge(parent, AVar(x)) if x == id => Edge(parent, value)
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
		case App(_, _) => mani
		case Define(name, args, body) => Define(name, args, eval(body))
		case ITE(pred, thn, els) => if(evalPred(pred)) eval(thn) else eval(els)
		case Class(name, args, body) => Class(name, args, eval(body))
	}


}
