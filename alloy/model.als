open util/boolean

sig Path {
  dirname: lone Path,
  isAncestor: Path
}

fact {
  // isAncestor is reflexive transitive closure of dirname
  all p:Path | p.isAncestor = p.*dirname
}

one sig Root extends Path {}
fact { no Root.dirname } // Root does not have any parent
fact { all p: Path | Root in p.isAncestor } // root is ancestor of every path

sig FS {
  id: one FS,
  err: lone FS
}
fact {
  id = FS <: iden
  all fs: FS | fs.err = none
}

abstract sig Test {
  eval: Path -> FS -> one Bool
}
one sig PExists, IsDir, IsRegularFile, IsLink extends Test {}

abstract sig Op {
  apply: Path -> FS -> lone FS
}
one sig Mkdir, Rmdir, Create, Delete, Link, Unlink extends Op {}

fun Filter[t: Test, p: Path]: FS -> lone FS {
  /* Filter is identity relation for tests that evaluate to true and
   * err for tests that evaluate to false
   */
  ({fs: FS | (fs->True) in p.(t.eval)} <: id) +
  ({fs: FS | (fs->False) in p.(t.eval)} <: err)
}

fun Seq[a, b: FS -> lone FS]: FS -> lone FS { a.b }
fun Opt[a, b: FS -> lone FS]: FS -> lone FS { a+b}

assert seq_id_r {
  all p: Path, op: Op | Seq[p.(op.apply), id] = p.(op.apply)
}

assert seq_id_l {
  all p: Path, op: Op | Seq[id, p.(op.apply)] = p.(op.apply)
}

assert seq_opt_dist_l {
  all p1, p2, p3: Path, op1, op2, op3: Op |
  Seq[p1.(op1.apply), Opt[p2.(op2.apply), p3.(op3.apply)]] =
    Opt[Seq[p1.(op1.apply), p2.(op1.apply)], Seq[p1.(op1.apply), p3.(op3.apply)]]
}

assert seq_opt_dist_r {
  all p1, p2, p3: Path, op1, op2, op3: Op |
    Seq[Opt[p1.(op1.apply), p2.(op2.apply)], p3.(op3.apply)] =
      Opt[Seq[p1.(op1.apply), p3.(op3.apply)], Seq[p2.(op2.apply), p3.(op3.apply)]]
}

fact ops_commute {
  all p1, p2: Path, op1, op2: Op |
    ((not p2 in p1.isAncestor) and (not p1 in p2.isAncestor)) =>
  	  Seq[p1.(op1.apply), p2.(op2.apply)] = Seq[p2.(op2.apply), p1.(op1.apply)]
}

fact and_is_seq {
  all p1, p2: Path, t1, t2: Test, fs: FS |
    (True = And[fs.(p1.(t1.eval)), fs.(p2.(t2.eval))]) =>
       id = Seq[Filter[t1, p1], Filter[t2, p2]]
    else
       err = Seq[Filter[t1, p1], Filter[t2, p2]]
}

fact or_is_opt {
  all p1, p2: Path, t1, t2: Test, fs: FS |
    (True = Or[fs.(p1.(t1.eval)), fs.(p2.(t2.eval))]) =>
       id = Seq[Filter[t1, p1], Filter[t2, p2]]
    else
       err = Seq[Filter[t1, p1], Filter[t2, p2]]
}

fact pred_op_commute {
  all p1, p2: Path, t: Test, op: Op |
    (p1 != p2) => Seq[Filter[t, p1], p2.(op.apply)] = Seq[p2.(op.apply), Filter[t, p1]]
}

pred sanitycheck {}
run sanitycheck
