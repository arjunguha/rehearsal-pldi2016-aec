;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Paths
(set-option :produce-proofs true)
(set-option :smt.macro-finder true)

(declare-datatypes () ((Path root a b c d)))

; paths are / /a /b /c /a/d
;(define-fun dirname ((p1 Path) (p2 Path)) Bool
;  (or (and (= p1 a) (= p2 root))
;      (and (= p1 b) (= p2 root))
;      (and (= p1 c) (= p2 root))
;      (and (= p1 d) (= p2 a))))

; (define-fun is-ancestor ((p1 Path) (p2 Path)) Bool
;  (or (= p1 p2)
;      (= root p2)
;      (= a d)))
(declare-fun is-ancestor (Path Path) Bool)
(assert (forall ((p1 Path) (p2 Path))
           (= (is-ancestor p1 p2)
               (or (= p1 p2)
                   (= root p2)
                   (= a d)))))


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

; (assert (forall ((p1 Path) (p2 Path))
;           (= (= p1 p2) (= (mkdir p1) (mkdir p2)))))

; seq is associative
(assert (forall ((a S) (b S) (c S)) (= (seq a (seq b c)) (seq (seq a b) c))))

(declare-fun mkdir (Path) S)

(echo "Expected sat:")
(check-sat)

(assert
 (forall ((p1 Path) (p2 Path))
   (if (and (not (is-ancestor p1 p2)) (not (is-ancestor p2 p1)))
       (= (seq (mkdir p1) (mkdir p2)) (seq (mkdir p2) (mkdir p1)))
       true)))


; (assert (forall ((p1 Path) (p2 Path))
;               (= (seq (mkdir p1) (mkdir p2))
;                  (seq (mkdir p2) (mkdir p1)))))


(echo "Expected SAT:")
(check-sat)






(push)
(assert (not (= (seq (mkdir a) (mkdir b)) (seq (mkdir b) (mkdir a)))))
(echo "Expected unsat:")
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
(echo "Expected unsat:")
(check-sat)
(pop)

(push)
(assert (not (= a b)))
(echo "Expected sat:")
(check-sat)
(get-model)
(pop)