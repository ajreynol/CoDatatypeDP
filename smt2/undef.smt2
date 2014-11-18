(set-logic ALL_SUPPORTED)
(declare-codatatypes () ((Lst (cons (hd Int) (tl Lst)) (nil1) (nil2))))

(assert (not (= (hd nil1) (hd nil2))))

(check-sat)
