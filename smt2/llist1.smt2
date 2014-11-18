(set-logic ALL_SUPPORTED)
(declare-codatatypes () ((Lst (cons (hd Int) (tl Lst)) (nil))))

(declare-fun xs () Lst)
(declare-fun ys () Lst)

(assert (= xs (cons 0 xs)))
(assert (= ys (cons 0 (cons 0 ys))))
(assert (not (= xs ys)))

(check-sat)
