package parser

import Syntax2._
import scalax.collection.mutable.Graph
import scalax.collection.mutable.Graph._
import scalax.collection.GraphEdge._

object Evaluator2 {

	case class EvalError(msg: String) extends RuntimeException(msg)
		type ManifestGraph = Graph[Manifest, DiEdge]

	def subExpr(varName: String, e: Expr, body: Expr): Expr = body match {
		case Str(_) => body
		case Res(typ, expr) => Res(typ, subExpr(varName, e, expr))
		case Var(id) if varName == id => e
		case Var(_) => body
		case Bool(_) => body
		case Not(expr) => Not(subExpr(varName, e, expr))
		case And(expr1, expr2) => And(subExpr(varName, e, expr1), subExpr(varName, e, expr2))
		case Or(expr1, expr2) => Or(subExpr(varName, e, expr1), subExpr(varName, e, expr2))
		case Eq(expr1, expr2) => Eq(subExpr(varName, e, expr1), subExpr(varName, e, expr2))
		case Match(expr1, expr2) => Match(subExpr(varName, e, expr1), subExpr(varName, e, expr2))
		case In(expr1, expr2) => In(subExpr(varName, e, expr1), subExpr(varName, e, expr2))
	}

	def subAttr(varName: String, e: Expr, attr: Attribute): Attribute = attr match {
		case Attribute(name, value) => Attribute(subExpr(varName, e, name), subExpr(varName, e, value))
	}	

	def sub(varName: String, e: Expr, body: Manifest): Manifest = body match {
		case Empty => body
		case Block(m1, m2) => Block(sub(varName, e, m1), sub(varName, e, m2))
		case Resource(typ, attrs) => Resource(typ, attrs.map(attr => subAttr(varName, e, attr)))
		case ITE(pred, m1, m2) => ITE(subExpr(varName, e, pred), sub(varName, e, m1), sub(varName, e, m2))
		case Edge(m1, m2) => Edge(sub(varName, e, m1), sub(varName, e, m2))
		case Define(name, params, m) => Define(name, params, sub(varName, e, m))
		case Let(v, expr, b) => Let(v, subExpr(varName, e, expr), sub(varName, e, b))
		case E(expr) => E(subExpr(varName, e, expr))
	}
	

	//a.name -> Str; a.value -> Constant|Res
	def evalAttr(a: Attribute): Attribute = a match {
		case Attribute(name, value) => Attribute(evalExpr(name), evalExpr(value))
	}

	def evalExpr(e: Expr): Expr = e match {
		case Res(typ, e) => Res(typ, evalExpr(e))
		case Var(_) => e
		case Str(_) => e
		case Bool(_) => e
		case Not(e) => evalExpr(e) match {
			case Bool(b) => Bool(!b)
			case _ => throw EvalError(s"Cannot evaluate: Invalid argument for Not: $e")
		}
		case And(e1, e2) => (evalExpr(e1), evalExpr(e2)) match {
			case (Bool(b1), Bool(b2)) => Bool(b1 && b2)
			case _ => throw EvalError(s"Cannot evaluate: Invalid argument(s) for And: $e1, $e2")
		}
		case Or(e1, e2) => (evalExpr(e1), evalExpr(e2)) match {
			case (Bool(b1), Bool(b2)) => Bool(b1 || b2)
			case _ => throw EvalError(s"Cannot evaluate: Invalid argument(s) for Or: $e1, $e2")
		}
		case Eq(e1, e2) => if(evalExpr(e1) == evalExpr(e2)) Bool(true) else Bool(false)
		case Match(Str(e1), Str(e2)) => {
			val pat = e2.r
			e1 match {
				case pat(_) => Bool(true)
				case _ => Bool(false)
			}
		}
		case Match(e1, e2) => throw EvalError(s"Cannot evaluate: Invalid argument(s) for Match: $e1, $e2")
		case In(Str(e1), Str(e2)) => if(e2.contains(e1)) Bool(true) else Bool(false)
		case In(e1, e2) => throw EvalError(s"Cannot evaluate: Invalid argument(s) for In: $e1, $e2")
	}
	
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
		case Resource(typ, attrs) => Resource(typ, attrs.map(evalAttr))
		case ITE(pred, m1, m2) if(evalExpr(pred) == Bool(true))  => eval(m1)
		case ITE(pred, m1, m2) if(evalExpr(pred) == Bool(false)) => eval(m2)
		case ITE(pred, _, _) => throw EvalError(s"Cannot evaluate: Invalid Predicate for if: $pred")
		case Edge(m1, m2) => Edge(eval(m1), eval(m2))
		case Define(_, _, _) => m
		case Let(varName, e, body) => eval(sub(varName, e, body))
		case E(e) => E(evalExpr(e))
	}

	def addEdges(g: ManifestGraph, e: Edge): ManifestGraph = e match {
		case Edge(Block(m11, m12), m2) => addEdges(g, Edge(m11, m2)) ++ addEdges(g, Edge(m12, m2))
		case Edge(m1, Block(m21, m22)) => addEdges(g, Edge(m1, m21)) ++ addEdges(g, Edge(m1, m22))
		case Edge(m1, m2) => g += DiEdge(m1, m2)
	}	

	def toGraph(g: ManifestGraph, m: Manifest): ManifestGraph = m match {
		case Empty => g
		case Block(m1, m2) => toGraph(g, m1) ++ toGraph(g, m2)
		case Resource(_, _) => g + m
		case e@Edge(_, _) => addEdges(g, e)
		case Define(n, p, b) => g
		case _ => g + m
	}	

	def expand(m: Manifest, d: Define): Manifest = m match {
		case Empty => Empty
		case Block(m1, m2) => Block(expand(m1, d), expand(m2, d))
		case Resource(typ, attrs) => d match {
			//*****************TODO: deal with arguments/attrs/params
			case Define(name, params, body) if name == typ => body
			case _ => m //otherwise do nothing
		}
		
		case ITE(pred, thn, els) => ITE(pred, expand(thn, d), expand(els, d))
		case Edge(m1, m2) => Edge(expand(m1, d), expand(m2, d))
		case Define(name, params, body) => Define(name, params, expand(body, d)) //do I need to say if(d.name != name)?
		case Let(x, e, body) => Let(x, e, expand(body, d))
		case E(Res(typ, e)) => m //do something?
		case E(_) => m
	}
	
}