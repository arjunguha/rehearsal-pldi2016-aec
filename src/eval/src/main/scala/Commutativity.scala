package eval

import java.nio.file.Path

private[eval] object Commutativity {

  type ReadSet = Set[Path]
  type WriteSet = Set[Path]
  type IdemSet = Set[Path]

  // Cacluates read, write and Idem sets simultaneously
  def exprFileSets(expr: Expr): (ReadSet, WriteSet, IdemSet) = expr match {
    case Error => (Set.empty, Set.empty, Set.empty)
    case Skip => (Set.empty, Set.empty, Set.empty)
    case Filter(a) => (a.readSet, Set.empty, Set.empty)
    case If(TestFileState(d1, IsDir), Skip, Mkdir(d2)) if d1 == d2 => (Set.empty, Set.empty, Set(d1))
    case If(TestFileState(d1, DoesNotExist), Mkdir(d2), Skip) if d1 == d2 => (Set.empty, Set.empty, Set(d1))
    case If(a, p, q) => (a.readSet ++ p.readSet ++ q.readSet,
                         p.writeSet ++ q.writeSet,
                         p.idemSet ++ q.idemSet)
    case Concur(p, q) => (p.readSet ++ q.readSet,
                          p.writeSet ++ q.writeSet,
                          p.idemSet ++ q.idemSet)
    // TODO(nimish) write sets of p and q could invalidate the idemSets of q and p respectively
    case Seq(p, q) => (p.readSet ++ q.readSet,
                       p.writeSet ++ q.writeSet,
                       p.idemSet ++ q.idemSet)
    case Alt(p, q) => (p.readSet ++ q.readSet,
                       p.writeSet ++ q.writeSet,
                       p.idemSet ++ q.idemSet)
    case Atomic(p) => (p.readSet, p.writeSet, p.idemSet)
    case Mkdir(path) => (Set.empty, Set(path), Set.empty)
    case CreateFile(path, _) => (Set.empty, Set(path), Set.empty)
    case Rm(path) => (Set.empty, Set(path), Set.empty)
    case Cp(src, dst) => (Set(src), Set(dst), Set.empty)
  }

  def predReadSet(pred: Pred): Set[Path] = {
    pred match {
      case True | False => Set()
      case And(a, b) => a.readSet ++ b.readSet
      case Or(a, b) => a.readSet ++ b.readSet
      case Not(a) => a.readSet
      case TestFileState(path, _) => Set(path)
    }
  }

  def commutes(p: Expr, q: Expr): Boolean = {

    val pr = p.readSet
    val pw = p.writeSet
    val qr = q.readSet
    val qw = q.writeSet
    val pi = p.idemSet
    val qi = q.idemSet

    // no write-write conflicts
    (pw intersect qw).isEmpty &&
    // no read-write conflicts
    (pr intersect qw).isEmpty && (pw intersect qr).isEmpty &&
    /* its ok to have same paths in idemSets for p and q
     * but any path in p expr's idemSet should not occur
     * in read and write set of q expr and vice versa.
     */
    (pi intersect qr).isEmpty && (pi intersect qw).isEmpty &&
    (pr intersect qi).isEmpty && (pw intersect qi).isEmpty
  }
}
