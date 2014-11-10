;(set-option :smt.macro-finder true)
(set-option :auto-config false)
(set-option :smt.ematching false)
(set-option :smt.mbqi true)
(set-option :smt.mbqi_max_iterations 10000000)

(declare-datatypes () ((Path root a b c d e f g)))

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

(declare-fun mkdir (Path) S)

(declare-fun Seqv (S S) Bool)


(assert (forall ((p1 Path) (p2 Path))
        (=> (not (= p1 p2))
            (not (Seqv (mkdir p1) (mkdir p2))))))

(assert (forall ((p1 Path) (p2 Path))
         (=> (Seqv (mkdir p1) (mkdir p2))
               (= p1 p2))))


; (assert (forall ((p1 Path) (p2 Path))
;         (! (=> (not (= p1 p2))
;             (not (Seqv (mkdir p1) (mkdir p2))))
;         :pattern (Seqv (mkdir p1) (mkdir p2)))))

; (assert (forall ((p1 Path) (p2 Path))
;         (! (=> (Seqv (mkdir p1) (mkdir p2))
;                (= p1 p2))
;         :pattern (Seqv (mkdir p1) (mkdir p2)))))

(push)
(assert (not (Seqv (mkdir a) (mkdir b))))
(check-sat)
(get-model)
(pop)

