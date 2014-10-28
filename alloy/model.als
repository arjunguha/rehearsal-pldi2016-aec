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
  apply: FS -> Path -> one Bool
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
  all fs: FS, p: Path, b: Bool, t: Test | b = p.(fs.(t.apply)) =>
    b = True => t.(Filter.apply) = Id and 
    b = False => t.(Filter.apply) = Err
}

one sig Seq, Opt {
  apply: Path -> Op -> Path -> Op -> FS -> FS
}


// Seq and Opt could be functions?

fact seq_def {
  // What is seq
  all p1, p2: Path, op1, op2: Op, fsinit, fsfinal: FS |
    Seq.apply = (p1->op1->p2->op2->fsinit->fsfinal) =>
      fsfinal = (fsinit.(p1.(op1.apply))).(p2.(op2.apply))
}

fact opt_def {
  // What is opt
  all p1, p2: Path, op1, op2: Op, fsinit, fsfinal: FS |
    Opt.apply = (p1->op1->p2->op2->fsinit->fsfinal) =>
      fsfinal = fsinit.(p1.(op1.apply)) or
      fsfinal = fsinit.(p2.(op2.apply))
}

pred sanitycheck {}
run sanitycheck

/*
fact seq_id {
  // How is fsfinal reached when Id op is involved with Seq
}

fact seq_err {
  // How is fsfinal reached when Err op is involved with Seq
}

fact opt_err {
  // How is fsfinal reached when Err op is involved with Seq
}

fact seq_assoc {
  // Seq is associative (seq a (seq b c)) = (seq (seq a b) c) 
  // TODO : Check? should follow from relational algebra : write a pred to confirm
  all a, b, c: FS | (c.(b.(Seq.apply))).(a.(Seq.apply)) = c.((b.(a.(Seq.apply))).(Seq.apply))
}

fact opt_assoc {
  // Opt is associative (opt a (opt b c)) = (opt (opt a b) c)
  // TODO: Check? Should follow from relational algebra : write a pred to confirm
  all a, b, c: FS | (c.(b.(Opt.apply))).(a.(Opt.apply)) = c.((b.(a.(Opt.apply))).(Opt.apply))
}

fact opt_commute {
  // TODO: Should follow from definition of opt : write a pred to confirm
  all fs1, fs2: FS | fs1.(fs2.(Opt.apply)) = fs2.(fs1.(Opt.apply))
}

fact opt_idem {
  all fs: FS | fs.(fs.(Opt.apply)) = fs
}

fact seq_dist_opt {
  // Seq is distributive over Opt
}


// if p1 not subpath p2 and p2 not subpath p1 then sequence of operations commute
fact {
  all fs, fs1, fs2, fs3, fs4: FS, p1, p2: Path, opA, opB: Op | 
    fs1 = fs.(p1.(opA.apply))   and
    fs2 = fs1.(p2.(opB.apply)) and
    fs3 = fs.(p2.(opB.apply))   and
    fs4 = fs3.(p1.(opA.apply)) and
    ((not p2 in p1.isAncestor) and (not p1 in p2.isAncestor)) =>
      fs2.(fs1.(Seq.apply)) = fs4.(fs3.(Seq.apply))
}

pred sanitycheck {}
run sanitycheck for 3

assert  doesnotcommute {
  all fsinit, fs1, fs2, fs3, fs4: FS, f, d: Path |
     fs1 = fsinit.(f.(Create.apply)) and
     fs2 = fs1.(d.(Mkdir.apply)) and
     fs3 = fsinit.(d.(Mkdir.apply)) and
     fs4 = fs3.(f.(Create.apply)) and
     d in f.dirname =>
       fs2.(fs1.(Seq.apply)) != fs4.(fs3.(Seq.apply))
}
check doesnotcommute for 3
*/
