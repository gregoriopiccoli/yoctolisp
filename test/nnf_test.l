(load "nnf.l")
(load "testsuite.l")
(load "NegNormForm.l")

(test-suite "--- old Negation normal form test suite ---"

  (test (nnf '(not(and a b))) '(or(not a)(not b))  "de morgan and")
  (test (nnf '(not(or a b)))  '(and(not a)(not b)) "de morgan or")
  (test (nnf '(not(not a)))   'a                   "not not a")
  (test (nnf '(-> a b))       '(or(not a) b)       "implicazione")
  (test (nnf '(not(and (not a) (and (not x) c)))) '(or a x (not c)) "or che non appiattisce")
  
)

(test-suite "--- Negation normal form test suite ---"

  (test (NegNormForm '(not(and a b))) '(or(not a)(not b))  "de morgan and")
  (test (NegNormForm '(not(or a b)))  '(and(not a)(not b)) "de morgan or")
  (test (NegNormForm '(not(not a)))   'a                   "not not a")
  (test (NegNormForm '(-> a b))       '(or(not a) b)       "implicazione")
  (test (NegNormForm '(not(and (not a) (and (not x) c))))  '(or a x (not c))         "or che non appiattisce")
  (test (NegNormForm '(not(and (< x 10) (= y 20))))        '(or (>= x 10) (<> y 20)) "< e >")
  
)

(test-suite "--- flatten test suite ---"

  (test (flatten '(and (and a b) c))        '(and a b c)         "flatten (and (and a b) c)")
  (test (flatOps '(+) '(+ (+ 1 2)(+ 3 4)))  '(+ 1 2 3 4)         "flatOps (+(+ 1 2)(+ 3 4)) (+)")

)

(test-suite "--- Tableaux test suite ---"

  (test (theo '(-> a (-> b a)))      t                   "a->(b->a) is a theorem")
  (test (theo '(-> (-> a b) a))     '(nil a)             "(a->b)->a fails, model (nil a)")

)

