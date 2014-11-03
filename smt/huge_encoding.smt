(set-option :timeout 2000)

(declare-sort Path)
(declare-sort FS)

(declare-const root Path)
(declare-const x Path)
(declare-const y Path)
(declare-const usr Path)
(declare-const sbin Path)

; How x, y and root are related
; x = /x
; y = /y
; usr = /usr
; sbin = /sbin

(declare-fun pexists (Path FS) Bool)

; FS0 is the initial filesystem and root definitely exists on FS0, can't say about anything else
(declare-const FS0 FS)
(assert (pexists root FS0))

(declare-fun mkdir (Path FS FS) Bool)

(declare-const FS1 FS)
; mkdir x FS0 FS1
(assert (=> (pexists root FS0) (pexists x FS1)))
(assert (and (= (pexists root FS0) (pexists root FS1))
             (= (pexists y FS0) (pexists y FS1))
             (= (pexists usr FS0) (pexists usr FS1))
             (= (pexists sbin FS0) (pexists sbin FS1))))

; mkdir x FS1 FS2
(declare-const FS2 FS)
(assert (=> (pexists root FS1) (pexists y FS2)))
(assert (and (= (pexists root FS1) (pexists root FS2))
             (= (pexists x FS1) (pexists x FS2))
             (= (pexists usr FS1) (pexists usr FS2))
             (= (pexists sbin FS1) (pexists sbin FS2))))

; mkdir x FS1 FS2
(declare-const FS3 FS)
(assert (=> (pexists root FS0) (pexists y FS3)))
(assert (and (= (pexists root FS0) (pexists root FS3))
             (= (pexists x FS0) (pexists x FS3))
             (= (pexists usr FS0) (pexists usr FS3))
             (= (pexists sbin FS0) (pexists sbin FS3))))

; mkdir x FS1 FS2
(declare-const FS4 FS)
(assert (=> (pexists root FS3) (pexists x FS4)))
(assert (and (= (pexists root FS3) (pexists root FS4))
             (= (pexists y FS3) (pexists y FS4))
             (= (pexists usr FS3) (pexists usr FS4))
             (= (pexists sbin FS3) (pexists sbin FS4))))
(echo "sanity check .. SAT expected")
(check-sat)

; FS2 and FS4 are equal
(assert (not (and (= (pexists root FS2) (pexists root FS4))
             	  (= (pexists x FS2) (pexists x FS4))
             	  (= (pexists y FS2) (pexists y FS4))
             	  (= (pexists usr FS2) (pexists usr FS4))
             	  (= (pexists sbin FS2) (pexists sbin FS4)))))
(echo "checking for equivalence .. UNSAT expected")
(check-sat)

