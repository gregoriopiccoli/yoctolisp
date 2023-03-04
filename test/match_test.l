(load "match.l")
(load "testsuite.l")

(test-suite "--- Match test suite ---"

(test (Match '(a b c) '(a b c))              nil                 "match di liste identiche senza variabili")
(test (Match '(a ?x c) '(a b c))             '((?x . b))         "match di liste con una variabile")
(test (Match '((a . ?x) . ?y) '((a . b). c)) '((?y . c)(?x . b)) "match di liste con struttura e due variabili in celle cons")
(test (Match '((a . ?x) . ?y) '((a   b)  c)) '((?y   c)(?x   b)) "match di liste con struttura e due variabili")
(test (Match 'a 'a)                          nil                 "match di atomi")
(test (Match '?x 'a)                         '((?x . a))         "match di variabile con atomo")
(test (Match '(1 . ?x)  '(1 . a))            '((?x . a))         "match di variabile con atomo in cella cons")

(test (Match '(1 2 3) '(2 3 4))              :failed             "match di liste diverse")
(test (Match '(?x ?x) '(1 2))                :failed             "matche di variabili che devono corrispondere")
(test (Match '((1 2) 3) '(1 2 3))            :failed             "strutture diverse")
(test (Match '(1 ?x 2) '(1 2 3))             :failed             "variabili non basta a rendere uguale")

(test (Match '(1 *x) '(1 2 3))               '((*x 2 3))         "jolly alla fine")
(test (Match '(1 . *x) '(1 2 3))             '((*x 2 3))         "jolly alla fine (atomo)")
(test (Match '(1 *x 2 3) '(1 2 3))           '((*x))             "jolly che non prende nulla")
(test (Match '(1 2 3 *x) '(1 2 3))           '((*x))             "jolly alla fine che non prende nulla")
(test (Match '(1 *x 2 3) '(1 a b c 2 3))     '((*x a b c))       "jolly prende lista")

(test (Match '*x 1)                          '((*x . 1))         "jolly con atomo")
(test (Match '(*x) 1)                        '((*x . 1))         "lista con jolly e atomo")
(test (Match '(*x) '(1 2 . 3))               '((*x 1 2 . 3))     "solo jolly con atomo finale")
(test (Match '(1 *x . 3) '(1 2 . 3))         '((*x 2))           "solo jolly con atomo finale")
(test (Match '(1 *x . 3) '(1 . 3))           '((*x))             "jolly nullo con atomo finale")

(test (Match '(a b (?x nump)) '(a b 1))      '((?x . 1))         "match con constraint")
(test (Match '(a b (?x nump)) '(a b c))      :failed             "match con constraint non rispettato")
(test (Match '((?x (lambda(x)(< x 10)))) '(9))   '((?x . 9))     "match con constraint con lambda")
(test (Match '((?x (lambda(x)(< x 10)))) '(11))  :failed         "match con constraint con lambda non rispettato")

(test (Match '(+ *h ?x ?x *t) '(+ y y))                                    '((*h)(*t)(?x . y))                       "espressione +")
(test (Match '(+ *h (* ?y ?x) ?x *t) '(+ 1 (* 2 x) x 2 3))                 '((*h 1) (*t 2 3) (?x . x) (?y . 2))      "espressione con + e *")
(test (Match '(and *h false *t) '(and (< a b) true (> b 1) false (= 1 1))) '((*h (< a b) true (> b 1)) (*t (= 1 1))) "and con false") 
(test (Match '(and *h1 ?x *h2 (not ?x) *t) '(and 1 a 2 (not a) 3))         '((*h1 1)(*h2 2)(*t 3)(?x . a))           "and con a e (not a)") 

(test (Match '(- (+ *h ?x *t) ?x ) '(- (+ a z) z))                         :failed        "pattern *h ?x *t, non riesce a trovare il match")
 
)


