;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; PathsG
(set-logic HORN)

(set-option :smt.macro-finder true)

(declare-sort Path)
(declare-const root Path)
(declare-const a Path)
(declare-const b Path)
(declare-const c Path)
(assert (distinct root a b c))

(declare-fun is-ancestor (Path Path) Bool)
(assert (forall ((p1 Path) (p2 Path))
           (= (is-ancestor p1 p2)
               (or (= p1 p2)
                   (= root p2)))))


; S is a file-system operation, or error
(declare-sort S)

(declare-fun Seqv (S S) Bool)

;(declare-sort Cmd)

(declare-const err S)
(declare-const id S)

(declare-fun seq (S S) S)


(declare-fun mkdir (Path) S)

(assert (forall ((a S)) (Seqv a a)))
(assert (forall ((a S) (b S)) (=> (Seqv a b) (Seqv b a))))


(assert (forall ((a S) (b S) (c S))
          (=> (and (Seqv a b) (Seqv b c))
              (Seqv a c))))

; ;(assert (= a b))
; ;(check-sat)


; ; Congruence for seq
; (assert (forall ((a S) (b S) (c S) (d S))
;           (=> (and (Seqv a c) (Seqv b d))
;               (Seqv (seq a b) (seq c d)))))

; ; id
(assert (forall ((op S)) (Seqv (seq op id) op)))
(assert (forall ((op S)) (Seqv (seq id op) op)))


; err is the zero

; seq is associative
;(assert (forall ((a S) (b S) (c S)) (Seqv (seq a (seq b c)) (seq (seq a b) c))))

; mkdir commutativity condition
(assert
 (forall ((p1 Path) (p2 Path))
   (=> (and (not (is-ancestor p1 p2)) (not (is-ancestor p2 p1)))
       (Seqv (seq (mkdir p1) (mkdir p2)) (seq (mkdir p2) (mkdir p1))))))

; mkdir is injective
(assert (forall ((p1 Path) (p2 Path)) (= (= p1 p2) (Seqv (mkdir p1) (mkdir p2)))))


(echo "Expected SAT:")
(check-sat)




(push)
; mkdir injective test
;(assert (= (mkdir a) (mkdir b)))
;(echo "Testing if mkdir is injective .. Expected unsat")
(assert (not (Seqv (mkdir a) (mkdir b))))
(echo "Testing if mkdir is injective")
;(check-sat-using (then qe smt))
(check-sat)
(pop)
