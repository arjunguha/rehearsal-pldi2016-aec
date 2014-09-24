(set-option :timeout 2000)
; (set-option :smt.macro-finder true)

; Types
(declare-sort String)
(declare-sort Path)
(declare-sort FS)
(declare-sort Content)

; Function declaration
(declare-fun mkdir (FS FS Path) Bool)
;(declare-fun pexists (FS Path) Bool)
(declare-fun create (FS FS Path Content) Bool)

(declare-const rootPath Path)

; dirname /etc/apache2 /etc = true
; dirname /etc /etc/apache2 = false
(declare-fun dirname (Path Path) Bool)

; / does not have a parent
(assert (forall ((p Path)) (= (dirname rootPath p) false)))

; Every path other than root has a parent
;(assert (forall ((p Path))
;          (=> (not (= p rootPath))
;              (exists ((parent Path))
;                       (dirname p parent)))))

(declare-fun issubpath (Path Path) Bool)

; (is-ancestor "/" "/bin") is true
; (is-ancestor "/bin" "/") is false
(declare-fun is-ancestor (Path Path) Bool)


(assert (forall ((dir Path) (parent Path))
         (=> (dirname dir parent) (is-ancestor parent dir))))

; is-ancestor is transitive
(assert
   (forall ((p1 Path) (p2 Path) (p3 Path))
      (=> (and (is-ancestor p1 p2) (is-ancestor p2 p3))
          (is-ancestor p1 p3))))

; no cycles
(assert (forall ((p1 Path) (p2 Path))
           (not (and (is-ancestor p1 p2) (is-ancestor p2 p1)))))


; every path is its own subpath
;(assert (forall ((p Path)) (issubpath p p)))

; issubpath is the reflexive closure of the is-ancestor relation
;(assert (forall ((dir Path) (parent Path))
;          (=> (is-ancestor parent dir)
;              (issubpath parent dir))))

(assert (forall ((p1 Path) (p2 Path))
           (=> (issubpath p1 p2)
               (or (= p1 p2) (is-ancestor p1 p2)))))


(push)
;---------------------------------------------------
(declare-const p1 Path)
(declare-const p2 Path)

;(assert (forall ((x Path))
;          (or (= x rootPath) (= x p1) (= x p2))))
(assert (not (= p1 rootPath)))
(assert (not (= p2 rootPath)))

(assert (issubpath p1 p2))
(assert (issubpath p2 p1))
(echo "Silly constraints check ... Please say SAT")
(check-sat)
(echo "Path equality test ... Please say UNSAT")
(assert (not (= p1 p2)))
(check-sat)
;----------------------------------------------------
(pop)

; ; issubpath is anti-symmetric
; (assert (forall ((p1 Path) (p2 Path))
;            (=> (and (issubpath p1 p2)
;                     (issubpath p2 p1))
;                (= p1 p2))))

;(assert (forall ((fs1 FS) (fs2 FS) (p Path) (c Content))
;           (=> (create fs1 fs2 p c) (pexists fs2 p))))

;(assert (forall ((fs1 FS) (fs2 FS) (p Path))
;           (=> (mkdir fs1 fs2 p) (pexists fs2 p))))

;parent of path is always its subpath
;(assert (forall ((p Path)) (issubpath (dirname p) p)))

; (assert (forall ((p Path)) (not (= (dirname p) p))))

; mkdir changes state when FS not already in desired state
;(assert (forall ((fs1 FS) (fs2 FS) (p Path))
;          (=> (and (not (pexists fs1 p)) (mkdir fs1 fs2 p)) (not (= fs1 fs2)))))

; createfile is idempotent
;(assert (forall ((fs1 FS) (fs2 FS) (fs3 FS) (p Path) (c Content))
;           (=> (and (create fs1 fs2 p c) (create fs2 fs3 p c)) (= fs2 fs3))))

; createfile is  injective
;(assert (forall ((fs1 FS) (fs2 FS) (fs3 FS) (p1 Path) (p2 Path) (c1 Content) (c2 Content))
;           (=> (and (create fs1 fs2 p1 c1) (create fs1 fs3 p2 c2) (not (= p1 p2)))
;               (not (= fs2 fs3)))))

; create commutes on distinct files
; (assert (forall ((fs1 FS) (fs2 FS) (fs3 FS) (fs4 FS) (fs5 FS) (p1 Path) (p2 Path) (c1 Content) (c2 Content))
;            (=> (and (create fs1 fs2 p1 c1) (create fs2 fs3 p2 c2)
;                     (create fs1 fs4 p2 c2) (create fs4 fs5 p1 c1)
;                     (not (= p1 p2)))
;                (= fs3 fs5))))

; mkdir is idempotent
(assert (forall ((fs1 FS) (fs2 FS) (fs3 FS) (p Path))
           (=> (and (mkdir fs1 fs2 p) (mkdir fs1 fs3 p)) (= fs2 fs3))))

; mkdir is injective
;(assert (forall ((fs1 FS) (fs2 FS) (fs3 FS) (p1 Path) (p2 Path))
;          (=> (and (mkdir fs1 fs2 p1) (mkdir fs1 fs3 p2) (not (= p1 p2)))
;              (not (= fs2 fs3)))))

; mkdir commutes on distinct files when parent not equal
(assert (forall ((fs1 FS) (fs2 FS) (fs3 FS) (fs4 FS) (fs5 FS) (p1 Path) (p2 Path))
          (=> (and (mkdir fs1 fs2 p1) (mkdir fs2 fs3 p2)
                   (mkdir fs1 fs4 p2) (mkdir fs4 fs5 p1)
                   (not (issubpath p1 p2))
                   (not (issubpath p2 p1)))
              (= fs3 fs5))))

; create and mkdir commute
; (assert (forall ((fs1 FS) (fs2 FS) (fs3 FS) (fs4 FS) (fs5 FS) (p1 Path) (p2 Path) (c Content))
;            (=> (and (not (= p1 p2))
;                     (not (issubpath p1 (dirname p2)))
;                     (not (issubpath (dirname p2) p1))
;                     (mkdir fs1 fs2 p1) (create fs2 fs3 p2 c)
;                     (create fs1 fs4 p2 c) (mkdir fs4 fs5 p1))
;                (= fs3 fs5))))


; create and exists commute
;(assert (forall ((fs1 FS) (fs2 FS) (fs3 FS) (p1 Path) (p2 Path) (c Content))
;           (=> (and (not (= p1 p2))
;                    (not (issubpath p1 (dirname p2)))
;                    (not (issubpath (dirname p2) p1))
;                    (pexists fs1 p1) (create fs1 fs2 p2 c)
;                    (create fs1 fs3 p2 c) (pexists fs3 p1))
;               (= fs2 fs3))))

; mkdir and exists commute
;(assert (forall ((fs1 FS) (fs2 FS) (fs3 FS) (p1 Path) (p2 Path) (c Content))
;           (=> (and (not (issubpath p1 p2))
;                    (not (issubpath p2 p1))
;                    (pexists fs1 p1) (mkdir fs1 fs2 p2)
;                    (mkdir fs1 fs3 p2) (pexists fs3 p1))
;               (= fs2 fs3))))

(echo "Checking model (sat expected) ...")
(check-sat)

(push)

(declare-const foo Path)
(declare-const bar Path)
(assert (not (= foo rootPath)))
(assert (not (= bar rootPath)))

;(assert (not (= foo bar)))
(assert (not (issubpath foo bar)))
(assert (not (issubpath bar foo)))

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

(echo "Checking validity of commutivity of mkdir. \"Unsat\" expected:")
(assert (not (= fs3 fs5)))

(check-sat)

(pop)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;; triplets commute ;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(push)
(declare-const foo Path)
(declare-const bar Path)
(declare-const baz Path)

(assert (not (= foo bar)))
(assert (not (= bar baz)))
(assert (not (= foo baz)))

(assert (not (= rootPath foo)))
(assert (not (= rootPath bar)))
(assert (not (= rootPath baz)))

(assert (not (issubpath foo bar)))
(assert (not (issubpath bar foo)))

(assert (not (issubpath bar baz)))
(assert (not (issubpath baz bar)))

(assert (not (issubpath foo baz)))
(assert (not (issubpath baz foo)))

(declare-const fs1 FS)
(declare-const fs2 FS)
(declare-const fs3 FS)
(declare-const fs4 FS)
(declare-const fs5 FS)
(declare-const fs6 FS)
(declare-const fs7 FS)

(assert (mkdir fs1 fs2 foo))
(assert (mkdir fs2 fs3 bar))
(assert (mkdir fs3 fs4 baz))

(assert (mkdir fs1 fs5 bar))
(assert (mkdir fs5 fs6 baz))
(assert (mkdir fs6 fs7 foo))

;(assert (mkdir fs1 fs5 foo))
;(assert (mkdir fs5 fs6 baz))
;(assert (mkdir fs6 fs7 bar))

(echo "Any silly contradictions? (sat expected)")
(check-sat)

(echo "Checking validity of commutivity of mkdir triplets. \"Unsat\" expected:")
(assert (not (= fs4 fs7)))
(check-sat)
; (get-model)
(pop)



; ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; ;;;;;;;;;;;;;;;;;;;;;; mkdir and create commutes ;;;;;;;;;;;;;;;;;;;;;;;
; ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; (push)
; ;----------------
; (declare-const foo Path)
; (declare-const bar Path)
; (assert (not (= foo bar)))
; (assert (not (issubpath foo (dirname bar))))
; (assert (not (issubpath (dirname bar) foo)))

; (declare-const fs1 FS)
; (declare-const fs2 FS)
; (declare-const fs3 FS)
; (declare-const fs4 FS)
; (declare-const fs5 FS)

; (declare-const c Content)

; (assert (mkdir fs1 fs2 foo))
; (assert (create fs2 fs3 bar c))

; (assert (create fs1 fs4 bar c))
; (assert (mkdir fs4 fs5 foo))

; (echo "Any silly contradictions? (sat expected)")
; (check-sat)

; (echo "Checking validity of commutivity of mkdir and create. \"Unsat\" expected:")
; (assert (not (= fs3 fs5)))

; (check-sat)


; (pop)



; ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; ;;;;;;;;;;;;;;;;;;;;;;;;;; User Commutivity Test, stage 1 ;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; (push)

; ; Initial file system
; (declare-const fs FS)

; ; Creation of user one
; (declare-const us1sysfile Path)
; (declare-const us1homedir Path)
; (assert (not (= us1sysfile us1homedir)))
; (assert (not (issubpath us1homedir (dirname us1sysfile))))
; (assert (not (issubpath (dirname us1sysfile) us1homedir)))

; ; Creation of user two
; (declare-const us2sysfile Path)
; (declare-const us2homedir Path)
; (assert (not (= us2sysfile us2homedir)))
; (assert (not (issubpath us2homedir (dirname us2sysfile))))
; (assert (not (issubpath (dirname us2sysfile) us2homedir)))

; ; system file for both user is not the same
; (assert (not (= us1sysfile us2sysfile)))
; ;(assert (not (issubpath us1sysfile us2sysfile)))
; ;(assert (not (issubpath us2sysfile us1sysfile)))

; ; homedir for both users is not the same
; (assert (not (= us1homedir us2homedir)))
; (assert (not (issubpath us1homedir us2homedir)))
; (assert (not (issubpath us2homedir us1homedir)))

; (assert (not (= us1homedir us2sysfile)))
; (assert (not (issubpath us1homedir (dirname us2sysfile))))
; (assert (not (issubpath (dirname us2sysfile) us1homedir)))

; (assert (not (= us2homedir us1sysfile)))
; (assert (not (issubpath us2homedir (dirname us1sysfile))))
; (assert (not (issubpath (dirname us1sysfile) us2homedir)))



; (declare-const fs2 FS)
; (declare-const fs3 FS)
; (declare-const fs4 FS)
; (declare-const fs5 FS)
; (declare-const fs7 FS)
; (declare-const fs8 FS)
; (declare-const fs9 FS)
; (declare-const fs10 FS)
; (declare-const fs11 FS)

; (declare-const cus1 Content)
; (declare-const cus2 Content)

; ; Sequence us1 then us2
; ;(assert (create fs fs2 us1sysfile cus1))
; (assert (mkdir fs fs3 us1homedir))
; (assert (create fs3 fs4 us2sysfile cus2))
; (assert (mkdir fs4 fs5 us2homedir))

; ; Sequence us2 then us1
; (assert (create fs fs7 us2sysfile cus2))
; (assert (mkdir fs7 fs8 us2homedir))
; ;(assert (create fs7 fs8 us1sysfile cus1))
; (assert (mkdir fs8 fs9 us1homedir))

; (echo "Any silly contradictions? (sat expected)")
; (check-sat)

; (echo "Checking commutativity of user creation step1. \"Unsat\" expected.")
; (assert (not (= fs9 fs5)))
; (check-sat)
; ; (get-model)
; (pop)





; ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; ;;;;;;;;;;;;;;;;;;;;;;;;;; User Commutivity Test ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; (push)

; ; Initial file system
; (declare-const fs FS)

; ; Creation of user one
; (declare-const us1sysdir Path)
; (declare-const us1systemsettings Path)
; (assert (= us1sysdir (dirname us1systemsettings)))

; (declare-const us1homedir Path)
; (assert (not (issubpath us1homedir us1sysdir)))
; (assert (not (issubpath us1sysdir us1homedir)))

; ;(assert (not (= us1systemsettings us1homedir)))
; ;(assert (not (= us1sysdir us1homedir)))
; ;(assert (not (= (dirname us1systemsettings) (dirname us1homedir))))
; ;(assert (not (issubpath (dirname us1systemsettings) us1homedir)))
; ;(assert (not (issubpath us1homedir (dirname us1systemsettings))))


; ; Creation of user two
; (declare-const us2sysdir Path)
; (declare-const us2systemsettings Path)
; (assert (= us2sysdir (dirname us2systemsettings)))

; (declare-const us2homedir Path)
; (assert (not (issubpath us2homedir us2sysdir)))
; (assert (not (issubpath us2sysdir us2homedir)))


; ;(assert (not (= us2systemsettings us2homedir)))
; ;(assert (not (= us2sysdir us2homedir)))
; ;(assert (not (= (dirname us2systemsettings) (dirname us2homedir))))
; ;(assert (= us2sysdir (dirname us2systemsettings)))
; ;(assert (not (issubpath (dirname us2systemsettings) us2homedir)))
; ;(assert (not (issubpath us2homedir (dirname us2systemsettings))))



; ; system directories for both user is not the same but their dirname directories are same
; (assert (not (= us1sysdir us2sysdir)))
; ;(assert (= (dirname us1sysdir) (dirname us2sysdir)))

; ; homedir for both users is not the same but thier dirname directories are
; (assert (not (= us1homedir us2homedir)))
; ;(assert (= (dirname us1homedir) (dirname us2homedir)))

; (assert (not (= us1systemsettings us2systemsettings)))

; (assert (not (issubpath us1homedir us2homedir)))
; (assert (not (issubpath us2homedir us1homedir)))

; (assert (not (issubpath us1sysdir us2sysdir)))
; (assert (not (issubpath us2sysdir us1sysdir)))

; (assert (not (issubpath us1systemsettings us2systemsettings)))
; (assert (not (issubpath us2systemsettings us1systemsettings)))


; (declare-const fs2 FS)
; (declare-const fs3 FS)
; (declare-const fs4 FS)
; (declare-const fs5 FS)
; (declare-const fs6 FS)
; (declare-const fs7 FS)
; (declare-const fs8 FS)
; (declare-const fs9 FS)
; (declare-const fs10 FS)
; (declare-const fs11 FS)
; (declare-const fs12 FS)
; (declare-const fs13 FS)

; (declare-const cus1 Content)
; (declare-const cus2 Content)

; ; Sequence us1 then us2
; ;(assert (and (not (pexists fs us1sysdir)) (mkdir fs fs2 us1sysdir)
; ;             (create fs2 fs3 us1systemsettings cus1)
; ;             (not (pexists fs3 us1homedir)) (mkdir fs3 fs4 us1homedir)))

; ;(assert (and (not (pexists fs4 us2sysdir)) (mkdir fs4 fs5 us2sysdir)
; ;             (create fs5 fs6 us2systemsettings cus2)
; ;             (not (pexists fs6 us2homedir)) (mkdir fs6 fs7 us2homedir)))


; ; Sequence us2 then us1
; ;(assert (and (not (pexists fs us2sysdir)) (mkdir fs fs8 us2sysdir)
; ;             (create fs8 fs9 us2systemsettings cus2)
; ;             (not (pexists fs9 us2homedir)) (mkdir fs9 fs10 us2homedir)))

; ;(assert (and (not (pexists fs10 us1sysdir)) (mkdir fs10 fs11 us1sysdir)
; ;             (create fs11 fs12 us1systemsettings cus1)
; ;             (not (pexists fs12 us1homedir)) (mkdir fs12 fs13 us1homedir)))

; (assert (not (pexists fs us1sysdir)))
; (assert (not (pexists fs us1systemsettings)))
; (assert (not (pexists fs us1homedir)))
; (assert (not (pexists fs us2sysdir)))
; (assert (not (pexists fs us2systemsettings)))
; (assert (not (pexists fs us2homedir)))


; ; Sequence us1 then us2
; (assert (mkdir fs fs2 us1sysdir))
; (assert (create fs2 fs3 us1systemsettings cus1))
; (assert (mkdir fs3 fs4 us1homedir))
; (assert (mkdir fs4 fs5 us2sysdir))
; (assert (create fs5 fs6 us2systemsettings cus2))
; (assert (mkdir fs6 fs7 us2homedir))


; ; Sequence us2 then us1
; (assert (mkdir fs fs8 us2sysdir))
; (assert (create fs8 fs9 us2systemsettings cus2))
; (assert (mkdir fs9 fs10 us2homedir))
; (assert (mkdir fs10 fs11 us1sysdir))
; (assert (create fs11 fs12 us1systemsettings cus1))
; (assert (mkdir fs12 fs13 us1homedir))

; (echo "Any silly contradictions? (sat expected)")
; (check-sat)

; (echo "Checking commutativity of user creation. \"Unsat\" expected.")
; (assert (not (= fs13 fs7)))
; (check-sat)
; ; (get-model)
; (pop)
