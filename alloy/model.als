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

sig FS {}

abstract sig Test {
  eval: FS -> Path -> one Bool
}

one sig PExists, IsDir, IsRegularFile, IsLink extends Test {}

abstract sig Op {
  apply: Path -> FS -> lone FS
}
one sig Mkdir, Rmdir, Create, Delete, Link, Unlink extends Op {}
one sig Id, Err extends Op {}

fact {
  all p: Path | p.(Id.apply) = FS <: iden
  all p: Path, fs: FS | fs.(p.(Err.apply)) = none
}

one sig Filter {
  apply: Test -> Op
}

fact {
  // filter gives either id or err depending on bool value
  all t: Test | (t.(Filter.apply) = Id) or (t.(Filter.apply) = Err)
  all fs: FS, p: Path, b: Bool, t: Test | b = p.(fs.(t.eval)) =>
    (b = True) => t.(Filter.apply) = Id and 
    (b = False) => t.(Filter.apply) = Err
}

fun Seq[p1, p2: Path, op1, op2: Op]: FS -> lone FS {
  ((op1 = Err) or (op2 = Err)) => Root.(Err.apply)
  else (p1.(op1.apply)).(p2.(op2.apply))
}

fun Opt[p1, p2: Path, op1, op2: Op]: FS -> lone FS {
    (op1 = Err) =>  p2.(op2.apply)
    else (op2 = Err) => p1.(op1.apply)
    else ((op1 = op2) and (p1 = p2)) => p1.(op1.apply)
    else Root.(Err.apply) // Special case when both options are valid then we dont select any
}

assert seq_id_r {
  all p1, p2: Path, op: Op |
    Seq[p1, p2, op, Id] = p1.(op.apply)
}

assert seq_id_l {
  all p1, p2: Path, op: Op |
    Seq[p1, p2, Id, op] = p2.(op.apply)
}

assert seq_opt_dist_l {
  // TODO
}

assert seq_opt_dist_r {
  // TODO
}

fact ops_commute {
  all p1, p2: Path, op1, op2: Op |
    ((not p2 in p1.isAncestor) and (not p1 in p2.isAncestor)) =>
  	  Seq[p1, p2, op1, op2] = Seq[p2, p1, op2, op1]
}

// TODO : Should be independent of FS
fact and_is_seq {
  all p1, p2: Path, t1, t2: Test, fs: FS |
    (True = And[p1.(fs.(t1.eval)), p2.(fs.(t2.eval))]) =>
       (p1.(Id.apply)) = Seq[p1, p2, t1.(Filter.apply), t2.(Filter.apply)]
    else
       (p1.(Err.apply)) = Seq[p1, p2, t1.(Filter.apply), t2.(Filter.apply)]
}

// TODO : Should be independent of FS
fact or_is_opt {
  all p1, p2: Path, t1, t2: Test, fs: FS |
    (True = Or[p1.(fs.(t1.eval)), p2.(fs.(t2.eval))]) =>
       (p1.(Id.apply)) = Seq[p1, p2, t1.(Filter.apply), t2.(Filter.apply)]
    else
       (p1.(Err.apply)) = Seq[p1, p2, t1.(Filter.apply), t2.(Filter.apply)]
}

fact pred_op_commute {
  all p1, p2: Path, t: Test, op: Op |
    (p1 != p2) => Seq[p1, p2, t.(Filter.apply), op] = Seq[p2, p1, op, t.(Filter.apply)]
}

pred sanitycheck {}
run sanitycheck
