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
//  id: lone FS,
//  err: lone FS
}

one sig Id, Err extends FS {}

/*
fact {
  id = FS <: iden
  all fs: FS | fs.err = none
}
*/

abstract sig Test {
  apply: FS -> Path -> one Bool
}

one sig PExists, IsDir, IsRegularFile, IsLink extends Test {}

abstract sig Op {
  apply: Path -> FS -> lone FS
}

fact {
  // applying any operation to Err FS results in error
  all op: Op, p: Path | Err.(p.(op.apply)) = Err
}

one sig Mkdir, Rmdir, Create, Delete, Link, Unlink extends Op {}
one sig Filter {
  apply: Test -> FS -> lone FS
}

fact {
  // filter gives either id or err depending on bool value
  all fs: FS, p: Path, b: Bool, t: Test | b = p.(fs.(t.apply)) =>
    b = True => fs.(t.(Filter.apply)) = fs and 
    b = False => fs.(t.(Filter.apply)) = Err
}


/*
// May e ID and Err needs to have same type and that of FS
one sig Id {
  apply: FS -> one FS
}
one sig Err {
  apply: FS -> lone FS
}


fact {
  Id.apply = FS <: iden
  all fs: FS | fs.(Err.apply) = none
}
*/


abstract sig Combinator {
  apply: FS -> FS -> FS
}

one sig Seq, Opt extends Combinator {}

fact seq_id {
  all fs: FS | fs.(Id.(Seq.apply)) = fs
  all fs: FS | Id.(fs.(Seq.apply)) = fs
}

fact seq_err {
  all fs: FS | fs.(Err.(Seq.apply)) = Err
  all fs: FS | Err.(fs.(Seq.apply)) = Err
}

fact opt_err {
  all fs: FS | fs.(Err.(Opt.apply)) = fs
  all fs: FS | Err.(fs.(Opt.apply)) = fs
}

fact seq_assoc {
  // Seq is associative (seq a (seq b c)) = (seq (seq a b) c) 
  all a, b, c: FS | (c.(b.(Seq.apply))).(a.(Seq.apply)) = c.((b.(a.(Seq.apply))).(Seq.apply))
}

fact opt_assoc {
  // Opt is associative (opt a (opt b c)) = (opt (opt a b) c)
  all a, b, c: FS | (c.(b.(Opt.apply))).(a.(Opt.apply)) = c.((b.(a.(Opt.apply))).(Opt.apply))
}

fact opt_commute {
  all fs1, fs2: FS | fs1.(fs2.(Opt.apply)) = fs2.(fs1.(Opt.apply))
}

fact opt_idem {
  all fs: FS | fs.(fs.(Opt.apply)) = fs
}

fact seq_dist_opt {
  // Seq is distributive over Opt
}


// if p1 not subpath p2 and p2 not subpath p1 then create and mkdir commute
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
