;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; PathsG
(set-option :timeout 3000)
(set-option :smt.auto-config false)
(set-option :smt.macro-finder true)
(set-option :smt.mbqi false)
(set-option :smt.ematching true)
;(set-option :model.compact true)

(declare-datatypes () ((Path root a b c u1 u2 uh1 uh2 us1 us2 g1 g2 gs1 gs2)))

; paths are / /a /b /c
(declare-fun dirname (Path Path) Bool)
(assert (forall ((p1 Path) (p2 Path))
           (= (dirname p1 p2)
              (or (and (= p1 a) (= p2 root))
                  (and (= p1 b) (= p2 root))
                  (and (= p1 c) (= p2 root))
                  (and (= p1 us1) (= p2 u1))
                  (and (= p1 us2) (= p2 u2))
                  (and (= p1 gs1) (= p2 g1))
                  (and (= p1 gs2) (= p2 g2))))))

;(define-fun is-ancestor ((p1 Path) (p2 Path)) Bool
;  (or (= p1 p2)
;      (= root p2)
;      (= a d)))
(declare-fun is-ancestor (Path Path) Bool)
(assert (forall ((p1 Path) (p2 Path))
           (= (is-ancestor p1 p2)
               (or (= p1 p2)
                   (= root p2)
                   (and (= p1 us1) (= p2 u1))
                   (and (= p1 us2) (= p2 u2))
                   (and (= p1 gs1) (= p2 g1))
                   (and (= p1 gs2) (= p2 g2))))))


; S is a file-system operation, or error
(declare-sort S)
(declare-sort Cmd)

(declare-fun err () S)
(declare-fun id () S)
(assert (distinct err id))

(declare-fun seq (S S) S)
(declare-fun opt (S S) S)

; seq is associative for all a, b and c
(assert (forall ((a S) (b S) (c S)) (= (seq a (seq b c)) (seq (seq a b) c))))

; opt is commutative for anything
(assert
  (forall ((s1 S) (s2 S))
     (= (opt s1 s2) (opt s2 s1))))

; seq is left distributive over opt
(assert
  (forall ((s1 S) (s2 S) (s3 S))
     (= (seq s1 (opt s2 s3)) (opt (seq s1 s2) (seq s1 s3)))))

; seq is right distributive over opt
(assert
  (forall ((s1 S) (s2 S) (s3 S))
     (= (seq (opt s1 s2) s3) (opt (seq s1 s3) (seq s2 s3)))))

; id is 1
(assert (forall ((op S)) (= (seq op id) op)))
(assert (forall ((op S)) (= (seq id op) op)))

; err is the zero
(assert (forall ((op S)) (= (seq op err) err)))
(assert (forall ((op S)) (= (seq err op) err)))

(assert (forall ((op S)) (= (opt op err) op)))


(declare-fun pexists (Path) S)
(declare-fun notpexists (Path) S)
(assert (forall ((p Path)) (distinct (pexists p) (notpexists p))))

;(assert (forall ((p Path))
;           (or (= (pexists p) id)
;               (= (pexists p) err))))

;(assert (forall ((p Path))
;           (or (= (notpexists p) id)
;               (= (notpexists p) err))))

;(assert (forall ((p Path))
;           (= (seq (pexists p) (notpexists p))
;               err)))
;(assert (forall ((p Path))
;           (= (opt (pexists p) (notpexists p))
;               id)))

;(declare-fun isdir (Path) S)
;(declare-fun isregularfile (Path) S)
;(declare-fun islink (Path) S)


(declare-fun mkdir (Path) S)
;(declare-fun rmdir (Path) S)
(declare-fun create (Path) S)
;(declare-fun delete (Path) S)
;(declare-fun link (Path) S)
;(declare-fun unlink (Path) S)
;(declare-fun shell (Cmd) S)


; mkdir is injective
;(assert
;  (forall ((p1 Path) (p2 Path))
;     (=> (not (= p1 p2))
;         (not (= (mkdir p1) (mkdir p2))))))

; seq is commutative for mkdir 
(assert
 (forall ((p1 Path) (p2 Path))
   (=> (and (not (is-ancestor p1 p2)) (not (is-ancestor p2 p1)))
       (= (seq (mkdir p1) (mkdir p2)) (seq (mkdir p2) (mkdir p1))))))



; seq is commutative for create
(assert
 (forall ((p1 Path) (p2 Path))
   (=> (and (not (is-ancestor p1 p2)) (not (is-ancestor p2 p1)))
       (= (seq (create p1) (create p2)) (seq (create p2) (create p1))))))


; seq is commutative for create and mkdir
(assert
  (forall ((p1 Path) (p2 Path))
    (=> (and (not (is-ancestor p1 p2)) (not (is-ancestor p2 p1)))
        (= (seq (mkdir p1) (create p2)) (seq (create p2) (mkdir p1))))))


; checking if directory exists and then creating is equal to creating a directory
;(assert
;  (forall ((p Path))
;     (= (seq (notpexists p) (mkdir p))
;        (mkdir p))))

; pexists check commutes with itself
(assert
  (forall ((p1 Path) (p2 Path))
     (= (seq (pexists p1) (pexists p2))
        (seq (pexists p2) (pexists p1)))))

; notpexists check commutes with itself
(assert
  (forall ((p1 Path) (p2 Path))
     (= (seq (notpexists p1) (notpexists p2))
        (seq (notpexists p2) (notpexists p1)))))

; notpexists commutes with pexists
(assert
  (forall ((p1 Path) (p2 Path))
     (= (seq (notpexists p1) (pexists p2))
        (seq (pexists p2) (notpexists p1)))))

; pexists commmutes with mkdir
(assert
  (forall ((p1 Path) (p2 Path))
     (=> (not (= p1 p2))
         (= (seq (pexists p1) (mkdir p2)) (seq (mkdir p2) (pexists p1))))))

; notpexists commmutes with mkdir
(assert
  (forall ((p1 Path) (p2 Path))
     (=> (not (= p1 p2))
         (= (seq (notpexists p1) (mkdir p2)) (seq (mkdir p2) (notpexists p1))))))


; pexists commutes with create
(assert
  (forall ((p1 Path) (p2 Path))
     (=> (not (= p1 p2))
         (= (seq (pexists p1) (create p2)) (seq (create p2) (pexists p1))))))

; notpexists commutes with create
(assert
  (forall ((p1 Path) (p2 Path))
     (=> (not (= p1 p2))
         (= (seq (notpexists p1) (create p2)) (seq (create p2) (notpexists p1))))))

;(echo "Expected SAT:")
;(check-sat)

(push)
(assert (not (not (= (seq (mkdir g1) (create gs2))
                     (seq (create gs2) (mkdir g1))))))
(echo "Checking negation of if mkdir and create commutes .. UNKNOWN expected")
(check-sat)
(pop)


(push)
(assert (not (= (seq (mkdir g1) (create gs2))
                (seq (create gs2) (mkdir g1)))))
(echo "Checking if mkdir and create commutes .. UNSAT expected")
(check-sat)
(pop)

(push)
(assert (not (not (= (seq (seq (mkdir g1) (create gs1)) (seq (mkdir g2) (create gs2)))
                  (seq (seq (mkdir g2) (create gs2)) (seq (mkdir g1) (create gs1)))))))
(echo "Checking negation of if creation commutes .. Expected UNKNOWN")
(check-sat)
(pop)


(push)
(assert (not (= (seq (seq (mkdir g1) (create gs1)) (seq (mkdir g2) (create gs2)))
                (seq (seq (mkdir g2) (create gs2)) (seq (mkdir g1) (create gs1))))))
(echo "Checking if creation commutes .. Expected UNSAT")
(check-sat)
(pop)


(push)
(assert (not (not (= (seq (opt (seq (mkdir g1) (create gs1)) (pexists g1))
                          (opt (seq (mkdir g2) (create gs2)) (pexists g2)))
                     (seq (opt (seq (mkdir g2) (create gs2)) (pexists g2))
                          (opt (seq (mkdir g1) (create gs1)) (pexists g1)))))))
(echo "Checking negation of if group creation commutes .. Expected UNKNOWN")
(check-sat)
(pop)


(push)
(assert (not (= (seq (opt (seq (mkdir g1) (create gs1)) (pexists g1))
                     (opt (seq (mkdir g2) (create gs2)) (pexists g2)))
                (seq (opt (seq (mkdir g2) (create gs2)) (pexists g2))
                     (opt (seq (mkdir g1) (create gs1)) (pexists g1))))))
(echo "Checking if group creation commutes .. Expected UNSAT")
(check-sat)
(pop)


(push)
(assert (not (not (= (seq (opt (seq (notpexists g1) (seq (mkdir g1) (create gs1))) (seq (pexists g1) id))
                          (opt (seq (notpexists g2) (seq (mkdir g2) (create gs2))) (seq (pexists g2) id)))
                     (seq (opt (seq (notpexists g2) (seq (mkdir g2) (create gs2))) (seq (pexists g2) id))
                          (opt (seq (notpexists g1) (seq (mkdir g1) (create gs1))) (seq (pexists g1) id)))))))
(echo "Checking negation of if group creation commutes .. Expected UNKNOWN")
(check-sat)
(pop)

(push)
(assert (not (= (seq (opt (seq (notpexists g1) (seq (mkdir g1) (create gs1))) (seq (pexists g1) id))
                     (opt (seq (notpexists g2) (seq (mkdir g2) (create gs2))) (seq (pexists g2) id)))
                (seq (opt (seq (notpexists g2) (seq (mkdir g2) (create gs2))) (seq (pexists g2) id))
                     (opt (seq (notpexists g1) (seq (mkdir g1) (create gs1))) (seq (pexists g1) id))))))
(echo "Checking if group creation commutes .. Expected UNSAT")
(check-sat)
(pop)


(push)
(assert (not (not (= (seq (opt (seq (seq (notpexists u1) (seq (mkdir u1) (create us1))) (opt (seq (notpexists uh1) (mkdir uh1)) (seq (pexists uh1) id))) (seq (pexists u1) id))
                     (opt (seq (seq (seq (notpexists u2) (mkdir u2)) (create us2)) (opt (seq (notpexists uh2) (mkdir uh2)) (seq (pexists uh2) id))) (seq (pexists u2) id)))
                (seq (opt (seq (seq (seq (notpexists u2) (mkdir u2)) (create us2)) (opt (seq (notpexists uh2) (mkdir uh2)) (seq (pexists uh2) id))) (seq (pexists u2) id))
                     (opt (seq (seq (seq (notpexists u1) (mkdir u1)) (create us1)) (opt (seq (notpexists uh1) (mkdir uh1)) (seq (pexists uh1) id))) (seq (pexists u1) id)))
))))
(echo "Testing negation of user creation commutes .. Expected SAT/UNKNOWN")
(check-sat)
(push)


(push)
(assert (not (= (seq (opt (seq (seq (notpexists u1) (seq (mkdir u1) (create us1))) (opt (seq (notpexists uh1) (mkdir uh1)) (seq (pexists uh1) id))) (seq (pexists u1) id))
                     (opt (seq (seq (seq (notpexists u2) (mkdir u2)) (create us2)) (opt (seq (notpexists uh2) (mkdir uh2)) (seq (pexists uh2) id))) (seq (pexists u2) id)))
                (seq (opt (seq (seq (seq (notpexists u2) (mkdir u2)) (create us2)) (opt (seq (notpexists uh2) (mkdir uh2)) (seq (pexists uh2) id))) (seq (pexists u2) id))
                     (opt (seq (seq (seq (notpexists u1) (mkdir u1)) (create us1)) (opt (seq (notpexists uh1) (mkdir uh1)) (seq (pexists uh1) id))) (seq (pexists u1) id)))
)))
(echo "Testing user creation commutes .. Expected Unsat")
(check-sat)
(push)
