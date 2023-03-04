(load "test.l")
(load "unify.l")

(defun rbe(tx ref rep elap)
  (progn
    (princln tx "=" elap " (" (* ref rep) ")" )
    elap
))

(defun bench-report(tt e)(princln "tot=" tt " exp=" e "  " (/ (* tt 100) e) "%" ""))

(defun be rl
  (let ((rep (if (null rl) 1 (car rl))))
  (bench-report(+

(rbe "mapcar-i" 2125 rep (time(dotimes(j (* rep 200000))
  (mapcar-i + '(1 2 3) '(1 2 3))
)))

(rbe "cons" 2416 rep (time(dotimes(j (* rep 10000000))
  (cons (cons 1 10) (cons 2 3))
)))

(rbe "ff" 1358 rep (time(dotimes(j (* rep 2000000))
  ((label ff(lambda(x)(if(atom x)x(ff(car x))))) '((1 . 2) . 3) )
)))

(rbe "mapcar-i" 2843 rep (time(dotimes(j (* rep 1000000))
  (mapcar-i + '(1))
)))
(rbe "mapcar" 1540 rep (time(dotimes(j (* rep 2000000))
  (mapcar + '(1 2 3) '(1 2 3))
)))

(rbe "unify" 2049 rep (time(dotimes(j (* rep 100000))
  (unify '(g(h(var x)(var y))(var k)) '(g(var z)1) nil)
)))
(rbe "fib" 3625 rep (time(dotimes(j (* rep 10))
  (fib 28)
)))
(rbe "sort" 2332 rep (time(dotimes(j (* rep 100000))
  (sort '(1 4 2 8 9 3 5 6 7 0))
)))
)
  (*(+ 2125 2416 1358 2843 1540 2049 3625 2332)rep)

)))

(princln "--- run alone ---")
(be)
