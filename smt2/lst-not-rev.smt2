(declare-datatypes () ((Lst (cons (hd Int) (tl Lst)) (nil))))

(declare-fun app (Lst Lst) Lst)
(assert (forall ((x Lst) (y Lst)) (! (= (app x y) (ite (is-cons x) (cons (hd x) (app (tl x) y)) y)) :fun-def)))

(declare-fun rev (Lst) Lst)
(assert (forall ((x Lst)) (! (= (rev x) (ite (is-cons x) (app (rev (tl x)) (cons (hd x) nil)) nil)) :fun-def)))


(declare-fun xs () Lst)

; the conjecture
(assert (not (= xs (rev xs))))

(check-sat)

