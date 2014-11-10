(set-option :fixedpoint.engine datalog)

; A tiny fragment of KA
(declare-datatypes ()
  ((S (err)
      (id)
      (seq (seq-e1 S) (seq-e2 S)))))

(declare-rel eqv (S S))

; A unique variable for each rule below, but it is totally unnecessary
(declare-var p S)
(declare-var q S)
(declare-var r S)
(declare-var s S)
(declare-var t S)

; Some KA axioms (not complete)
(rule (eqv (seq err p) err) err_left_zero)
(rule (eqv (seq q err) err) err_right_zero)
(rule (eqv (seq r id) r) id_right_one)
(rule (eqv (seq id s) s) id_left_one)

(rule (eqv t t) refl)

(query (eqv id id) :print-answer true)
; Output:
; unknown
; approximated relations
; If you remove the id_*_one rules, it produces sat
