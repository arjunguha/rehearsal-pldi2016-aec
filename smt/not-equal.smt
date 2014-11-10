; Need to convert this to
;(set-option :smt.macro-finder true)


(declare-datatypes () ((Path root a b c d)))

(declare-fun is-ancestor (Path Path) Bool)
(assert (forall ((p1 Path) (p2 Path))
           (= (is-ancestor p1 p2)
               (or (= p1 p2)
                   (= root p2)
                   (= a d)))))

(declare-sort S)

(declare-fun seq (S S) S)

(assert (forall ((a S) (b S) (c S)) (= (seq a (seq b c)) (seq (seq a b) c))))

(declare-fun mkdir (Path) S)

(assert
 (forall ((p1 Path) (p2 Path))
   (if (and (not (is-ancestor p1 p2)) (not (is-ancestor p2 p1)))
       (= (seq (mkdir p1) (mkdir p2)) (seq (mkdir p2) (mkdir p1)))
       true)))

(check-sat)
