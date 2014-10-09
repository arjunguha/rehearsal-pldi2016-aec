;(set-option :smt.macro-finder true)
(set-option :auto-config false)
(set-option :smt.mbqi.max-iterations 10)

(declare-datatypes () ((Path root a b c)))

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

(declare-sort S)

(declare-fun seq (S S) S)

(declare-fun Seqv (S S) Bool)
(declare-const id S)
(declare-const err S)

(assert (forall ((a S)) (Seqv a a)))
(assert (forall ((a S) (b S)) (= (Seqv a b) (Seqv b a))))
(assert (forall ((a S) (b S) (c S))
          (=> (and (Seqv a b) (Seqv b c))
              (Seqv a c))))
(assert (forall ((a S) (b S) (c S) (d S))
          (=> (and (Seqv a c) (Seqv b d))
              (Seqv (seq a b) (seq c d)))))

(assert (forall ((a S) (b S) (c S)) (Seqv (seq a (seq b c)) (seq (seq a b) c))))
(assert (forall ((op S)) (Seqv (seq op id) op)))


(assert (forall ((op S)) (Seqv (seq op id) op)))
(assert (forall ((op S)) (Seqv (seq id op) op)))

(assert (forall ((op S)) (Seqv (seq op err) err)))
(assert (forall ((op S)) (Seqv (seq err op) err)))

(declare-fun mkdir (Path) S)

(assert
 (forall ((p1 Path) (p2 Path))
   (=> (and (not (is-ancestor p1 p2)) (not (is-ancestor p2 p1)))
       (Seqv (seq (mkdir p1) (mkdir p2)) (seq (mkdir p2) (mkdir p1))))))


(assert (forall ((p1 Path) (p2 Path))
        (=> (not (= p1 p2))
            (not (Seqv (mkdir p1) (mkdir p2))))))

; (echo "Sanity check (all axioms SAT?)")
; (check-sat)

; (push)
; (assert (= a b))
; (check-sat)
; (pop)

; (push)
; (assert (Seqv (mkdir a) (mkdir b)))
; (check-sat)
; (pop)

(push)
(assert (not (not (Seqv (mkdir a) (mkdir b)))))
(check-sat)
(pop)

(push)
(assert (not (Seqv (mkdir a) (mkdir b))))
(check-sat)
(pop)
