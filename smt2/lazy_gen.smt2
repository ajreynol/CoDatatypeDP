(set-logic ALL_SUPPORTED)
(declare-codatatypes () ((Lst (cons (hd Int) (tl Lst)) (nil))))
(assert (forall ((x Int) (xs Lst)) (not (= xs (cons x xs)))))
(check-sat)
