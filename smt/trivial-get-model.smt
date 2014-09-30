(declare-const x Bool)
(declare-const y Bool)

(assert (or (= x y) (not (= x y))))
(check-sat)
(get-model)
