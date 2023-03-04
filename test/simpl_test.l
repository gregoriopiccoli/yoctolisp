(load "simpl.l")
(load "testsuite.l")

(test-suite "--- Arithmetic simpl ---"

(test (se '(+ 1 2 3))                              6                            "numeric add")
(test (se '(+ 1 (* 2 3)))                          7                            "numeric add&mult")
(test (se '(* 1 2 2 (+ 2 3 x)))                    '(+ 20 (* 4 x))              "distribuzione (*(+))")
(test (se '(*(+ x 2) x 3 x))                       '(+ (* 3 (^ x 3)) (* 6 (^ x 2)))   "distribuzione (*(+ ) ... )")
(test (se '(*(+ x 2) (+ x 3)))                     '(+ (^ x 2) (* 5 x) 6)       "distribuzione (*(+ )(+ )")
(test (se '(+(*(- 4 3) x)(* (- (/ y y) 1)z)))      'x                           "divisione y / y")
(test (se '(- 10 (+ 1 x 3)))                       '(- 6 x)                     "sottrazione con somma nel sottraendo")
(test (se '(-(+ 3 x 4) x))                         7                            "sottrazione con somma nel minuendo")
(test (se '(-(* 3 x 4) x))                         '(* 11 x)                    "sottrazione con moltiplicazione nel minuendo")

(test (se '(- (* (+ 1 2 3 x) (+ y z)) (* 6 z)))    '(+ (* 6 y) (* x y) (* x z)) "sottrazione di distribuzione * +")
(test (se '(+ 1 2 x (* 1 y)(- 10 8 (- y x) 7)))    '(+ -2 (* 2 x))              "doppia sottrazione")

(test (se '(- (- 5 5 5 y 7 0) x 0 x))              '(- -12 x x y)               "sottrazione di sottrazione")

)
