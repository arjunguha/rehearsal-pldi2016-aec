(set-option :timeout 2000)

; Types
(declare-sort String)

(declare-sort FS)
(declare-sort Content)

(declare-sort Path)

(declare-fun mkdir (FS FS Path) Bool)


(declare-const root Path)
(declare-const a Path)
(declare-const b Path)
(declare-const c Path)

(assert (distinct a b c root))

(assert (forall ((x Path))
          (or (= x root)
              (= x a)
              (= x b)
              (= x c))))

; paths are /a /b /c
(define-fun dirname ((p1 Path) (p2 Path)) Bool
  (or (and (= p1 a) (= p2 root))
      (and (= p1 b) (= p2 root))
      (and (= p1 c) (= p2 root))))


; (is-ancestor "/" "/bin") is true
; (is-ancestor "/bin" "/") is false
(declare-fun is-ancestor (Path Path) Bool)

; is-ancestor is the transitive closure of dirname
(assert
   (forall ((p1 Path) (p2 Path) (p3 Path))
      (= (or (and (is-ancestor p1 p2) (is-ancestor p2 p3))
               (dirname p3 p1))
           (is-ancestor p1 p3))))


; no cycles in in-ancestor
(assert (forall ((p1 Path) (p2 Path))
           (not (and (is-ancestor p1 p2) (is-ancestor p2 p1)))))


; mkdir is injective
(assert (forall ((fs1 FS) (fs2 FS) (fs3 FS) (p Path))
          (=> (and (mkdir fs1 fs2 p) (mkdir fs1 fs3 p))
              (= fs2 fs3))))

;mkdir commutes on distinct files when parent not equal
(assert (forall ((fs1 FS) (fs2 FS) (fs3 FS) (fs4 FS) (fs5 FS) (p1 Path) (p2 Path))
          (=> (and (mkdir fs1 fs2 p1) (mkdir fs2 fs3 p2)
                   (mkdir fs1 fs4 p2) (mkdir fs4 fs5 p1)
                   (not (is-ancestor p1 p2))
                   (not (is-ancestor p2 p1)))
              (= fs3 fs5))))

(echo "Sanity check (sat):")

(check-sat)

(push)


(declare-const fs1 FS)
(declare-const fs2 FS)
(declare-const fs3 FS)
(declare-const fs4 FS)
(declare-const fs5 FS)

(assert (mkdir fs1 fs2 a))
(assert (mkdir fs2 fs3 b))
(assert (mkdir fs1 fs4 b))
(assert (mkdir fs4 fs5 a))

(assert (not (= fs3 fs5)))

(echo "Expected unsat below:")
(check-sat)
(pop)

(declare-const fs1 FS)
(declare-const fs2 FS)
(declare-const fs3 FS)
(declare-const fs4 FS)
(declare-const fs5 FS)
(declare-const fs6 FS)
(declare-const fs7 FS)

(assert (mkdir fs1 fs2 a))
(assert (mkdir fs2 fs3 b))
(assert (mkdir fs3 fs4 c))

(assert (mkdir fs1 fs5 c))
(assert (mkdir fs5 fs6 a))
(assert (mkdir fs6 fs7 b))

(assert (not (= fs4 fs7)))
(echo "Expected unsat below:")
(check-sat)
