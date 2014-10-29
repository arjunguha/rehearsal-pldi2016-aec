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
fun App[op: Op, p: Path]: FS -> lone FS { p.(op.apply) }

fun Filter[t: Test, p: Path]: FS -> lone FS {
  /* Filter is identity relation for tests that evaluate to true and
   * err for tests that evaluate to false
   */
  ({fs: FS | (fs->True) in p.(t.eval)} <: id) +
  ({fs: FS | (fs->False) in p.(t.eval)} <: err)
}

fun NotFilter[t: Test, p: Path]: FS -> lone FS {
  ({fs: FS | (fs->True) in p.(t.eval)} <: err) +
  ({fs: FS | (fs->False) in p.(t.eval)} <: id)
}

assert {
  all p: Path, t: Test | Filter[t, p] + NotFilter[t, p] = id
  all p: Path, t: Test | Filter[t, p] & NotFilter[t, p] = err
}

fun Seq[a, b: FS -> lone FS]: FS -> lone FS { a.b }
fun Opt[a, b: FS -> lone FS]: FS -> lone FS { a+b}

/* associativity properties for seq and opt follows from relational algebra */
/* commutativity of opt follows from relational algebra */
/* commutativity of seq is defined below */

assert seq_id_r {
  all p: Path, op: Op | Seq[App[op, p], id] = App[op, p]
}

assert seq_id_l {
  all p: Path, op: Op | Seq[id, App[op, p]] = App[op, p]
}

assert seq_opt_dist_l {
  all p1, p2, p3: Path, op1, op2, op3: Op |
  Seq[App[op1, p1], Opt[App[op2, p2], App[op3, p3]]] =
    Opt[Seq[App[op1, p1], App[op2, p2]], Seq[App[op1, p1], App[op3, p3]]]
}

assert seq_opt_dist_r {
  all p1, p2, p3: Path, op1, op2, op3: Op |
    Seq[Opt[App[op1, p1], App[op2, p2]], App[op3, p3]] =
      Opt[Seq[App[op1, p1], App[op3, p3]], Seq[App[op2, p2], App[op3, p3]]]
}

fact ops_commute {
  all p1, p2: Path, op1, op2: Op |
    ((not p2 in p1.isAncestor) and (not p1 in p2.isAncestor)) =>
  	  Seq[App[op1, p1], App[op2, p2]] = Seq[App[op2, p2], App[op1, p1]]
}

/*
fact and_is_seq {
  all p1, p2: Path, t1, t2: Test, fs: FS |
    (True = And[fs.(p1.(t1.eval)), fs.(p2.(t2.eval))]) =>
       id = Seq[Filter[t1, p1], Filter[t2, p2]]
    else
       err = Seq[Filter[t1, p1], Filter[t2, p2]]
}
*/

fact and_is_seq {
  all p1, p2: Path, t1, t2: Test |
    Filter[t1, p1] & Filter[t2, p2] = Seq[Filter[t1, p1], Filter[t2, p2]]
}

/*
fact or_is_opt {
  all p1, p2: Path, t1, t2: Test, fs: FS |
    (True = Or[fs.(p1.(t1.eval)), fs.(p2.(t2.eval))]) =>
       id = Opt[Filter[t1, p1], Filter[t2, p2]]
    else
       err = Opt[Filter[t1, p1], Filter[t2, p2]]
}
*/

fact or_is_opt {
  all p1, p2: Path, t1, t2: Test |
    Filter[t1, p1] + Filter[t2, p2] = Opt[Filter[t1, p1], Filter[t2, p2]]
}

fact pred_op_commute {
  all p1, p2: Path, t: Test, op: Op |
    (p1 != p2) => Seq[Filter[t, p1], App[op, p2]] = Seq[App[op, p2], Filter[t, p1]]
}

pred sanitycheck {}
run sanitycheck

fun CreateGroup[dir, settings: Path]: FS -> lone FS {
  Opt[Seq[NotFilter[PExists, dir], Seq[App[Mkdir, dir], App[Create, settings]]],
         Seq[Filter[PExists, dir], id]]
}

pred group_creation_commutes {
  all u1settings, u1dir, u2settings, u2dir: Path |
  	dirname = u1settings->u1dir + u2settings->u2dir =>
  		Seq[CreateGroup[u1dir, u1settings], CreateGroup[u2dir, u2settings]] =
  		Seq[CreateGroup[u2dir, u2settings], CreateGroup[u1dir, u1settings]]
}

run group_creation_commutes


// Also take group into account
fun CreateUser[dir, settings, homedir: Path]: FS -> lone FS {
  Opt[Seq[Seq[NotFilter[PExists, dir], Seq[App[Mkdir, dir], App[Create, settings]]],
                 Opt[Seq[NotFilter[PExists, homedir], App[Mkdir, homedir]],
                        Seq[Filter[PExists, homedir], id]]],
         Seq[Filter[PExists, dir], id]]
}

pred user_creation_commutes {
  all u1dir, u1settings, u1homedir, u2dir, u2settings, u2homedir: Path |
    dirname = u1settings->u1dir + u2settings->u2dir =>
    Seq[CreateUser[u1dir, u1settings, u1homedir], CreateUser[u2dir, u2settings, u2homedir]] =
    Seq[CreateUser[u2dir, u2settings, u2homedir], CreateUser[u1dir, u1settings, u1homedir]]
}

run user_creation_commutes

// TODO : the predicate holds but it shouldn't
pred shouldnotcommute {
  all u1dir, u1settings, u1homedir, file: Path |
    dirname = u1settings -> u1dir + file->u1homedir =>
      Seq[CreateUser[u1dir, u1settings, u1homedir], App[Create, file]] =
      Seq[App[Create, file], CreateUser[u1dir, u1settings, u1homedir]]
}

run shouldnotcommute


