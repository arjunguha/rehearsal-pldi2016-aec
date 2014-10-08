;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Paths
;(set-option :smt.mbqi true)

(declare-datatypes () ((Path root a b c)))

; paths are / /a /b /c
(declare-fun dirname (Path Path) Bool)
(assert (forall ((p1 Path) (p2 Path))
           (= (dirname p1 p2)
              (or (and (= p1 a) (= p2 root))
                  (and (= p1 b) (= p2 root))
                  (and (= p1 c) (= p2 root))))))

;(define-fun is-ancestor ((p1 Path) (p2 Path)) Bool
;  (or (= p1 p2)
;      (= root p2)
;      (= a d)))
(declare-fun is-ancestor (Path Path) Bool)
(assert (forall ((p1 Path) (p2 Path))
           (= (is-ancestor p1 p2)
               (or (= p1 p2)
                   (= root p2)))))


; S is a file-system operation, or error
(declare-sort S)
(declare-sort Cmd)

(declare-fun err () S)
(declare-fun id () S)

(declare-fun seq (S S) S)
(declare-fun opt (Bool S S) S)

(declare-fun pexists (Path) Bool)
(declare-fun isdir (Path) Bool)
(declare-fun isregularfile (Path) Bool)
(declare-fun islink (Path) Bool)


(declare-fun mkdir (Path) S)
(declare-fun rmdir (Path) S)
(declare-fun create (Path) S)
(declare-fun delete (Path) S)
(declare-fun link (Path) S)
(declare-fun unlink (Path) S)
(declare-fun shell (Cmd) S)

(assert (forall ((op S)) (= (seq op id) op)))

; err is the zero
(assert (forall ((op S)) (= (seq op err) err)))
(assert (forall ((op S)) (= (seq err op) err)))



; seq is associative
(assert (forall ((a S) (b S) (c S)) (= (seq a (seq b c)) (seq (seq a b) c))))


; mkdir is injective
(assert
  (forall ((p1 Path) (p2 Path))
     (=> (not (= p1 p2))
         (not (= (mkdir p1) (mkdir p2))))))

(assert
 (forall ((p1 Path) (p2 Path))
   (=> (and (not (is-ancestor p1 p2)) (not (is-ancestor p2 p1)))
       (= (seq (mkdir p1) (mkdir p2)) (seq (mkdir p2) (mkdir p1))))))

(assert
 (forall ((p1 Path) (p2 Path))
   (=> (and (not (is-ancestor p1 p2)) (not (is-ancestor p2 p1)))
       (= (seq (create p1) (create p2)) (seq (create p2) (create p1))))))




;(echo "Expected SAT:")
;(check-sat)

(push)
; mkdir injective test
;(assert (= (mkdir a) (mkdir b)))
;(echo "Testing if mkdir is injective .. Expected unsat")
(assert (not (= (mkdir a) (mkdir b))))
(echo "Testing if mkdir is injective")
(check-sat)
(pop)
