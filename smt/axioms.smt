(declare-sort Path)

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
