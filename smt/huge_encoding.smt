(set-option :timeout 2000)

(declare-sort Path)
(declare-sort FS)

(declare-const root Path)
(declare-const x Path)
(declare-const y Path)
(declare-const usr Path)
(declare-const sbin Path)

(assert (distinct root x y usr sbin))

; How x, y and root are related
; x = /x
; y = /y
; usr = /usr
; sbin = /sbin

(declare-fun pexists (Path FS) Bool)

; FS0 is the initial filesystem and root definitely exists on FS0, can't say about anything else
(declare-const FS0 FS)
;(assert (pexists root FS0))

; parent should exist for child to exist
(assert (=> (not (pexists root FS0)) (and (not (pexists x FS0))
                                          (not (pexists y FS0))
                                          (not (pexists usr FS0))
                                          (not (pexists sbin FS0)))))

; Define an error filesystem
(declare-const FSERR FS)
(assert (not (pexists root FSERR)))
(assert (not (pexists x FSERR)))
(assert (not (pexists y FSERR)))
(assert (not (pexists usr FSERR)))
(assert (not (pexists sbin FSERR)))



(declare-const FS1 FS)
; parent should exist for a child to exist
(assert (=> (not (pexists root FS1)) (and (not (pexists x FS1))
                                          (not (pexists y FS1))
                                          (not (pexists usr FS1))
                                          (not (pexists sbin FS1)))))

; mkdir x FS0 FS1
; If parent dir exists then mkdir will be successful and resulting FS will
; resemble quite a bit to input FS
; If parent dir does not exists then mkdir will fail and we will have an
; error FS
(assert (=> (pexists root FS0) (and (pexists x FS1)
                                    (= (pexists root FS0) (pexists root FS1))
                                    (= (pexists y FS0) (pexists y FS1))
                                    (= (pexists usr FS0) (pexists usr FS1))
                                    (= (pexists sbin FS0) (pexists sbin FS1)))))
(assert (=> (not (pexists root FS0)) (and (= (pexists root FSERR) (pexists root FS1))
                                          (= (pexists y FSERR) (pexists y FS1))
                                          (= (pexists x FSERR) (pexists x FS1))
                                          (= (pexists usr FSERR) (pexists usr FS1))
                                          (= (pexists sbin FSERR) (pexists sbin FS1)))))


(declare-const FS2 FS)
; parent dir should exist for child to exist
(assert (=> (not (pexists root FS2)) (and (not (pexists x FS2))
                                          (not (pexists y FS2))
                                          (not (pexists usr FS2))
                                          (not (pexists sbin FS2)))))

; mkdir y FS1 FS2
; If parent dir exists then mkdir will be successful and resulting FS will
; resemble quite a bit to input FS
; If parent dir does not exists then mkdir will fail and we will have an
; error FS
(assert (=> (pexists root FS1) (and (pexists y FS2)
                                    (= (pexists root FS1) (pexists root FS2))
                                    (= (pexists x FS1) (pexists x FS2))
                                    (= (pexists usr FS1) (pexists usr FS2))
                                    (= (pexists sbin FS1) (pexists sbin FS2)))))
(assert (=> (not (pexists root FS1)) (and (= (pexists root FSERR) (pexists root FS2))
                                          (= (pexists y FSERR) (pexists y FS2))
                                          (= (pexists x FSERR) (pexists x FS2))
                                          (= (pexists usr FSERR) (pexists usr FS2))
                                          (= (pexists sbin FSERR) (pexists sbin FS2)))))

(declare-const FS3 FS)
;parent dir should exist for child to exist
(assert (=> (not (pexists root FS3)) (and (not (pexists x FS3))
                                          (not (pexists y FS3))
                                          (not (pexists usr FS3))
                                          (not (pexists sbin FS3)))))


; mkdir y FS0 FS3
; If parent dir exists then mkdir will be successful and resulting FS will
; resemble quite a bit to input FS
; If parent dir does not exists then mkdir will fail and we will have an
; error FS
(assert (=> (pexists root FS0) (and (pexists y FS3)
                                    (= (pexists root FS0) (pexists root FS3))
                                    (= (pexists x FS0) (pexists x FS3))
                                    (= (pexists usr FS0) (pexists usr FS3))
                                    (= (pexists sbin FS0) (pexists sbin FS3)))))
(assert (=> (not (pexists root FS0)) (and (= (pexists root FSERR) (pexists root FS3))
                                          (= (pexists y FSERR) (pexists y FS3))
                                          (= (pexists x FSERR) (pexists x FS3))
                                          (= (pexists usr FSERR) (pexists usr FS3))
                                          (= (pexists sbin FSERR) (pexists sbin FS3)))))


(declare-const FS4 FS)
;parent dir should exist for child to exist
(assert (=> (not (pexists root FS4)) (and (not (pexists x FS4))
                                          (not (pexists y FS4))
                                          (not (pexists usr FS4))
                                          (not (pexists sbin FS4)))))


; mkdir x FS3 FS4
; If parent dir exists then mkdir will be successful and resulting FS will
; resemble quite a bit to input FS
; If parent dir does not exists then mkdir will fail and we will have an
; error FS
(assert (=> (pexists root FS3) (and (pexists x FS4)
                                    (= (pexists root FS3) (pexists root FS4))
                                    (= (pexists y FS3) (pexists y FS4))
                                    (= (pexists usr FS3) (pexists usr FS4))
                                    (= (pexists sbin FS3) (pexists sbin FS4)))))
(assert (=> (not (pexists root FS3)) (and (= (pexists root FSERR) (pexists root FS4))
                                          (= (pexists y FSERR) (pexists y FS4))
                                          (= (pexists x FSERR) (pexists x FS4))
                                          (= (pexists usr FSERR) (pexists usr FS4))
                                          (= (pexists sbin FSERR) (pexists sbin FS4)))))

(echo "sanity check .. SAT expected")
(check-sat)

; check if FS2 and FS4 are equal
(assert (not (and (= (pexists root FS2) (pexists root FS4))
             	  (= (pexists x FS2) (pexists x FS4))
             	  (= (pexists y FS2) (pexists y FS4))
             	  (= (pexists usr FS2) (pexists usr FS4))
             	  (= (pexists sbin FS2) (pexists sbin FS4)))))
(echo "checking for equivalence .. UNSAT expected")
(check-sat)
