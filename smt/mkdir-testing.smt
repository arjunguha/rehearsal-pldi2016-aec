(set-option :timeout 2000)
; Types:

(declare-sort Path)
(declare-sort FS)

(declare-fun mkdir (FS FS Path) Bool)

; mkdir changes state
(assert (forall ((fs1 FS) (fs2 FS) (p Path))
          (=> (mkdir fs1 fs2 p) (not (= fs1 fs2)))))


; mkdir is injective
(assert (forall ((fs1 FS) (fs2 FS) (fs3 FS) (p1 Path) (p2 Path))
          (=> (and (mkdir fs1 fs2 p1) (mkdir fs1 fs3 p2) (not (= p1 p2)))
              (not (= fs2 fs3)))))

; mkdir commutes on distinct files
(assert (forall ((fs1 FS) (fs2 FS) (fs3 FS) (fs4 FS) (fs5 FS) (p1 Path) (p2 Path))
          (=> (and (mkdir fs1 fs2 p1) (mkdir fs2 fs3 p2)
                   (mkdir fs1 fs4 p2) (mkdir fs4 fs5 p1)
                   (not (= p1 p2)))
              (= fs3 fs5))))


(declare-const foo Path)
(declare-const bar Path)
(assert (not (= foo bar)))

(declare-const fs1 FS)
(declare-const fs2 FS)
(declare-const fs3 FS)
(declare-const fs4 FS)
(declare-const fs5 FS)

(assert (mkdir fs1 fs2 foo))
(assert (mkdir fs2 fs3 bar))
(assert (mkdir fs1 fs4 bar))
(assert (mkdir fs4 fs5 foo))

(echo "Any silly contradictions? (sat expected)")
(check-sat)

(echo "Unsat expected:")
(assert (not (= fs3 fs5)))

(check-sat)


