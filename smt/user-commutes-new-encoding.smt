(set-option :timeout 2000)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Paths

(declare-datatypes () ((Path root a b c d e usr1dir usr1set usr1hom usr2dir usr2set usr2hom)))

; paths are / /a /b /c /a/d /a/e /usr1dir/usr1set /usr2dir/usr2set /usr1hom /usr2hom
(define-fun dirname ((p1 Path) (p2 Path)) Bool
  (or (and (= p1 a) (= p2 root))
      (and (= p1 b) (= p2 root))
      (and (= p1 c) (= p2 root))
      (and (= p1 d) (= p2 a))
      (and (= p1 e) (= p2 a))
      (and (= p1 usr1set) (= p2 usr1dir)) ; usr1set resides inside usr1dir
      (and (= p1 usr2set) (= p2 usr2dir)) ; usr2set resides inside usr2dir
      (and (= p1 usr1dir) (= p2 root))
      (and (= p1 usr2dir) (= p2 root))
      (and (= p1 usr1hom) (= p2 root))
      (and (= p1 usr2hom) (= p2 root))))

(define-fun is-ancestor ((p1 Path) (p2 Path)) Bool
  (or (= p1 p2)
      (= root p2)
      (= a d)
      (= a e)))


(echo "Sanity check")
(check-sat)
;;;;;;;;;;;;;;;;;;;;;;;;;;;
; File system operations
;

; S is a file-system operation, or error
(declare-sort S)

(declare-fun err () S)
(declare-fun seq (S S) S)

; err is the zero
(assert (forall ((op S)) (= (seq op err) err)))
(assert (forall ((op S)) (= (seq err op) err)))

; seq is associative
(assert (forall ((a S) (b S) (c S)) (= (seq a (seq b c)) (seq (seq a b) c))))

(declare-fun mkdir (Path) S)

; mkdir is commutative
(assert
 (forall ((p1 Path) (p2 Path))
   (=> (and (not (is-ancestor p1 p2)) (not (is-ancestor p2 p1)))
       (= (seq (mkdir p1) (mkdir p2)) (seq (mkdir p2) (mkdir p1))))))

(declare-fun create (Path) S)

; create is commutative
(assert
  (forall ((p1 Path) (p2 Path))
    (=> (and (not (is-ancestor p1 p2)) (not (is-ancestor p2 p1)))
        (= (seq (create p1) (create p2)) (seq (create p2) (create p1))))))

; mkdir and create commutes
(assert
  (forall ((p1 Path) (p2 Path))
    (=> (and (not (is-ancestor p1 p2)) (not (is-ancestor p1 p2)))
        (= (seq (mkdir p1) (create p2)) (seq (create p2) (mkdir p1))))))

; (assert (forall ((p1 Path) (p2 Path))
;               (= (seq (mkdir p1) (mkdir p2))
;                  (seq (mkdir p2) (mkdir p1)))))

(echo "Expected SAT:")
(check-sat)


(push)
(assert (not (= (seq (mkdir a) (mkdir b)) (seq (mkdir b) (mkdir a)))))
(echo "Testing \"2 mkdir ops commute\". Expected unsat:")
(check-sat)
(pop)

(push)
(assert (not (= (seq (mkdir a) (seq (mkdir b) (mkdir c)))
                (seq (mkdir a) (seq (mkdir c) (mkdir b))))))
(echo "Expected unsat:")
(check-sat)
(pop)

(push)
(assert (not (= (seq (mkdir a) (seq (mkdir b) (mkdir c)))
                (seq (mkdir b) (seq (mkdir a) (mkdir c))))))
(echo "Expected unsat:")
(check-sat)
(pop)


(push)
(assert (not (= (seq (mkdir a) (seq (mkdir c) (mkdir b)))
                (seq (mkdir b) (seq (mkdir a) (mkdir c))))))
(echo "Testing \"3 mkdir ops commute\". Expected unsat:")
(check-sat)
(pop)


(push)
; user creation commutes => usr1 creation followed by user2 creation is same as user2 creation followed by user1 creation
; usr1dir -> usr1set -> usr1hom -> usr2dir -> usr2set -> usr2hom

(assert (not (= (seq (mkdir usr1dir) (seq (create usr1set) (seq (mkdir usr1hom) (seq (mkdir usr2dir) (seq (create usr2set) (mkdir usr2hom))))))
                (seq (mkdir usr2dir) (seq (create usr2set) (seq (mkdir usr2hom) (seq (mkdir usr1dir) (seq (create usr1set) (mkdir usr1hom)))))))))
(echo "Testing \"creating of users commute\". Expected unsat:")
(check-sat)
(pop)
