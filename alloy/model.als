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
  mkdir: Path -> FS,
  create: Path -> FS
}

// if p1 not subpath p2 and p2 not subpath p1 then create and mkdir commute
fact {
  all fs: FS, p1, p2: Path | 
    ((not p2 in p1.isAncestor) and (not p1 in p2.isAncestor)) implies
      p1.((p2.(fs.mkdir)).create) = p2.((p1.(fs.create)).mkdir)
}

pred sanitycheck {}
run sanitycheck for 10

assert  doesnotcommute {
  all a, b: Path | b in a.dirname implies no fs: FS | b.((a.(fs.create)).mkdir) = a.((b.(fs.mkdir)).create)
}
check doesnotcommute for 10
