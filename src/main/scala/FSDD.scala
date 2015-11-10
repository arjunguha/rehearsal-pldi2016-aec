package rehearsal

import FSSyntax._

trait NodeLike[A, X] {
  def restrict(a: TestFileState, b: Boolean): X
  def applyOp(other: X)(op: (A, A) => A): X
}

trait LeafLike[N, A] {
  def unapply(x: N): Option[A]
  def apply(x: A): N
}

trait BranchLike[N, A] {
  def unapply(x: N): Option[(TestFileState, N, N)]
  def apply(x: TestFileState, lo: N, hi: N): N
}

trait FSBDD[A] {


  type Node <: NodeLike[A, Node]

  val Leaf: LeafLike[Node, A]
  val Branch: BranchLike[Node, A]


  def cacheSize: Int

  def gc(roots: List[Node]): Int

}

trait SemiRing[A] {

  val zero: A
  val one: A
//  def sum(x: A, y: A): A
//  def mul(x: A, y: A): A
}


object FSBDD {

  def apply[A ](implicit semiring: SemiRing[A]): FSBDD[A] = new FSBDDImpl[A](semiring)

}

private class FSBDDImpl[A](semiring: SemiRing[A]) extends FSBDD[A] {

  import scala.collection.mutable.Map

  sealed trait Rep
  case class IBranch(a: TestFileState, lo: Node, hi: Node) extends Rep
  case class ILeaf(x: A) extends Rep


  case class Node(n: Int) extends NodeLike[A, Node] {

    def restrict(a: TestFileState, aValue: Boolean) = {
      val TestFileState(p1, s1) = a
      def recur(n: Node): Node = toRep(n) match {
        case ILeaf(_) => n
        case IBranch(b@TestFileState(p2, s2), lo, hi) => {
          p1.compareTo(p2) match {
            case 0 => s1.compare(s2) match {
              case 0 => {
                if (aValue) { hi } else { lo }
              }
              // When TestFileState(p1, s1) is true, TestFileState(p1, s2) is
              // gauranteed to be false. But, when TestFileState(p1, s1) is
              // false, TestFileState(p1, s2) may be true or false
              case _ => {
                if (aValue) { lo } else { node(b, recur(lo), recur(hi)) }
              }
            }
            case _ => node(b, recur(lo), recur(hi))
          }
        }
      }
      recur(this)
    }

    def applyOp(other: Node)(op: (A, A) => A): Node = {
      val dpTable = Map[(Node, Node), Node]()

      def recur(lhs: Node, rhs: Node) = dpTable.get(lhs -> rhs) match {
        case Some(node) => node
        case None => {
          val result = body(lhs, rhs)
          dpTable += (lhs, rhs) -> result
          result
        }
      }

      def normCompare(n: Int) = if (n > 0) 1 else if (n < 0) -1 else 0

      def body(lhs: Node, rhs: Node): Node  = (toRep(lhs), toRep(rhs)) match {
        case (ILeaf(b1), ILeaf(b2)) => {
          leaf(op(b1, b2))
        }
        case (ILeaf(_), IBranch(x, lo, hi)) => {
          node(x, recur(lhs, lo), recur(lhs, hi))
        }
        case (IBranch(x, lo, hi), ILeaf(_))  => {
          node(x, recur(lo, rhs), recur(hi, rhs))
        }
        case (IBranch(a1@TestFileState(p1, s1), lo1, hi1), IBranch(a2@TestFileState(p2, s2), lo2, hi2)) => {
          normCompare(p1.compareTo(p2)) match {
            case 0 => {
              s1.compare(s2) match {
                case 0 => node(a1, recur(lo1, lo2), recur(hi1, hi2))
                // when TestFileState(p2, s2) is true, we know that TestFileState(p1, s1) will be false, so we use
                // lo1 instead of lhs
                case 1 => node(a2, recur(lhs, lo2), recur(lo1, hi2))
                case -1 => node(a1, recur(lo1, rhs), recur(hi1, lo2))
                case n => throw Unexpected(s"comparison returned $n")
              }
            }
            case 1 => node(a2, recur(lhs, lo2), recur(lhs, hi2))
            case -1 => node(a1, recur(lo1, rhs), recur(hi1, rhs))
            case n => throw Unexpected(s"comparison returned $n")
          }
        }
      }

      recur(this, other)
    }

  }

  var nextIndex = 0
  val t = Map[Node, Rep]()
  val h = Map[Rep, Node]()

  def cacheSize = t.size

  def toNode(bdd: Rep): Node = {
    h.get(bdd) match {
      case Some(n) => n
      case None => {
        val n = Node(nextIndex)
        nextIndex = nextIndex + 1
        h += (bdd -> n)
        t += (n -> bdd)
        n
      }
    }
  }

  // Guaranteed not to fail, if all values of type Node are constructed by toNode.
  def toRep(n: Node): Rep = t(n)

  def leaf(x: A): Node = toNode(ILeaf(x))

  def mkTest(x: TestFileState): Node = toNode(IBranch(x, leaf(semiring.zero), leaf(semiring.one)))

  def node(a: TestFileState, lo: Node, hi: Node): Node = {
    if (lo == hi) {
      lo
    }
    else {
      toNode(IBranch(a, lo, hi))
    }
  }

  object Leaf extends LeafLike[Node, A] {
    def unapply(n: Node) = t.get(n) match {
      case Some(ILeaf(a)) => Some(a)
      case _ => None
    }

    def apply(x: A): Node = toNode(ILeaf(x))
  }

  object Branch extends BranchLike[Node, A] {
    def unapply(n: Node): Option[(TestFileState, Node, Node)] = {
      t.get(n) match {
        case Some(IBranch(a, lo, hi)) => Some((a, lo, hi))
        case _ => None
      }
    }

    def apply(a: TestFileState, lo: Node, hi: Node) = {
      if (lo == hi) {
        lo
      }
      else {
        def op(x: A, y: A) = {
          if (x == semiring.zero) {
            semiring.zero
          }
          else if (x == semiring.one) {
            y
          }
          else {
            throw Unexpected("expected zero or one on LHS")
          }
        }
        val lhs = node(a, leaf(semiring.one), leaf(semiring.zero)).applyOp(lo)(op)
        val rhs = node(a, leaf(semiring.zero), leaf(semiring.one)).applyOp(hi)(op)
        lhs.applyOp(rhs) { (x, y) =>  if (x == semiring.zero) y else x }
      }
    }
  }

  def gc(roots: List[Node]): Int = {
    def reachable(worklist: List[Node], reached: Set[Node]): Set[Node] = worklist match {
      case Nil => reached
      case n :: rest => {
        if (reached.contains(n)) {
          reachable(rest, reached)
        }
        else {
          toRep(n) match {
            case ILeaf(_) => reachable(rest, reached + n)
            case IBranch(_, lo, hi) => {
              reachable(lo :: hi :: rest, reached + n)
            }
          }
        }
      }
    }
    val reachableNodes = reachable(roots, Set())
    reachableNodes.size
  }

  override def toString(): String = {
    val buf = new StringBuilder()
    for ((k, v) <- t) {
      buf.append(k)
      buf.append(" -> ")
      buf.append(v)
      buf.append('\n')
    }
    buf.toString
  }
}