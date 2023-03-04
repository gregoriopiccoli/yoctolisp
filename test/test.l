(load "testsuite.l")

; -- alcune funzioni utili --

(defun dbl(x) (+ x x))

(defun ff(x)(cond
    ((atom x)x)
    (t(ff(car x)))))

(defun fib(n)(if   
    (< n 2) 
    1 
    (+ (fib(- n 1))(fib(- n 2)))))

(defun map-i(f l)
  (if (null l)
      nil
      (cons (f (car l))(map-i f (cdr l)))))

(defun mapcar-i (f . lsts)
  ((label mapcar-
          (lambda (lsts)
            (cond ((null lsts) (f))
                  ((atom (car lsts)) (car lsts))
                  (t (cons (apply f (map-i car lsts))
                           (mapcar- (map-i cdr lsts)))))))
   lsts))

(defun member-i (item lst)
  (cond ((atom lst) nil)
        ((eq (car lst) item) lst)
        (t (member-i item (cdr lst)))))

(defun equal-i(a b)
  (if (and (not (atom a)) (not (atom b)))
      (and (equal-i (car a) (car b))
           (equal-i (cdr a) (cdr b)))
    (eq a b)))

(defun filter-i (pred lst)
  (cond ((null lst) nil)
        ((not (pred (car lst))) (filter-i pred (cdr lst)))
        (t (cons (car lst) (filter-i pred (cdr lst))))))

(defun sublis(asc lst)
  (cond ((null lst) nil)
        ((atom lst)(sublis-atom lst (assoc lst asc)))
        (t(cons(sublis asc (car lst))(sublis asc (cdr lst))))))
(defun sublis-atom(a v)
  (cond ((null v)a)
  (t (cdr v))))

(defun lambdalambda(x)((lambda(y)(+ x y)) 10))

(defun counter()(let((x 0))(lambda()(setq x (+ x 1)))))
(setq cnt1 (counter))
(setq cnt2 (counter))
(if (lexical-scoping)(cnt1))

(defun tc_t1(x y z)(+ x y z))
(defun tc_t2(x)(lambda(y z)(tc_t1 x y z)))
(defun tc_t3(x)(tc_t2 x))
(defun tc_t4(x y)(lambda(z)((tc_t3 x) y z)))
(defun tc_t5(x y z)((tc_t4 x y) z))

(defun count-down(x)(if(= x 0)0(count-down(- x 1))))

(setq maze '((3 1)(0 4 2)(1 5)(0 4)(1 3)(2 8)(7 -1)(6 8)(7 5)))
 
(defun solve-maze(p s m)(cond
   ((eq p -1) s)
   ((member p s) nil)
   (t (do ((r (nth p m) (cdr r))
           (pp nil      (solve-maze (car r) (cons p s) m))) 
        ((or (null r) (not(null pp))) pp)
      )  
   )
)) 

; -- test suite --
(test-suite "-- Standard test suite --"

(test (dbl 1) 2 "test dbl")
(test (ff '((a.b).c)) 'a "test ff")

(test ((lambda(x y)(cons x y)) 1 2) '(1 . 2) "param test1" )
(test ((lambda(x . y)(cons x y)) 1 2) '(1 2) "param test2" )
(test ((lambda(x . y)(cons x y)) 1 2 3)  '(1 2 3) "param test3" )
(test ((lambda(x . y)(cons x y)) 1) '(1) "param test4" )

(test (< "alfa" "beta") t "test < str" )
(test (<= "alfa" "beta") t "test <= str" )
(test (>= "alfa" "beta") nil "test >= str")
(test (> "alfa" "beta") nil "test > str")
(test (< 1 2) t "test < int" )
(test (<= 1 2) t "test <= int" )
(test (>= 1 2) nil "test >= int" )
(test (> 1 2) nil "test > int" )
(test (< 'alfa 'beta) t "test < sym" )
(test (<= 'alfa 'beta) t "test <= sym" )
(test (>= 'alfa 'beta) nil "test >= sym")
(test (> 'alfa 'beta) nil "test > sym")

(test (+ 1 2 3) 6 "test (+ 1 2 3)")
(test (+ (+ 1 2) 3) 6 "test (+ (+ 1 2) 3)")

(test ((macro(tt th el)(if (eval tt) th el))(eq 1 1) (+ 1 1) aaaaa) 2 "test macro execution 1")
(test ((macro(tt th el)(if (eval tt) th el))(eq 1 0) aaaaa (+ 1 1)) 2 "test macro execution 2")

(test (append '(1 2 3) '(4 5 6)) '(1 2 3 4 5 6) "test append 1")

(test (member 3 '(1 2 3 4)) '(3 4) "test member 1")
(test (member 3 '(1 2 4)) nil "test member 2")
(test (member-i 3 '(1 2 3 4)) '(3 4) "test member-i 1")
(test (member-i 3 '(1 2 4)) nil "test member-i 2")

(test (map dbl '(1 2 3 4)) '(2 4 6 8) "test map 1")

(test (filter (lambda(x)(< x 10)) '(10 3 20 11 2 12 33 1)) '(3 2 1) "test filter")

(test (equal '((1 . 2) . 3) '((1 . 2) . 3)) t "test equal 1")
(test (equal '((1 . 2) . 3) '(1 . 2)) nil "test equal 2")
(test (equal '((1 . 3) . 2) '((1 . 2) . 3)) nil "test equal 3")
(test (equal '((1 . 3) . 2) 1) nil "test equal 4")
(test (equal 1 1) t "test equal 5")
(test (equal 1 2) nil "test equal 6")
(test (equal () nil) t "test equal 7")
(test (equal '(1 2) nil) nil "test equal 8")
(test (equal '(1 2) '(1 2)) t "test equal 9")
(test (equal '(1 2) '(1 . 2)) nil "test equal 10")

(test (equal-i '((1 . 2) . 3) '((1 . 2) . 3)) t "test equal-i 1")
(test (equal-i '((1 . 2) . 3) '(1 . 2)) nil "test equal-i 2")
(test (equal-i '((1 . 3) . 2) '((1 . 2) . 3)) nil "test equal-i 3")
(test (equal-i '((1 . 3) . 2) 1) nil "test equal-i 4")
(test (equal-i 1 1) t "test equal-i 5")
(test (equal-i 1 2) nil "test equal-i 6")
(test (equal-i () nil) t "test equal-i 7")
(test (equal-i '(1 2) nil) nil "test equal-i 8")
(test (equal-i '(1 2) '(1 2)) t "test equal-i 9")
(test (equal-i '(1 2) '(1 . 2)) nil "test equal-i 10")

(test (lambdalambda 1) 11 "test lambdalambda 1")

(if (lexical-scoping) (test (cnt1) 2 "test let over lambda 1") t)
(if (lexical-scoping) (test (cnt2) 1 "test let over lambda 2") t)
(if (lexical-scoping) (test (((lambda(x)(lambda(y)(+ x y))) 1) 2) 3 "test currying") t)

(test ((label zzz (lambda(x)(if (atom x) x (zzz(car x))))) '((a.b).c)) 'a "test label")

(test (mapcar-i + '(1 2 3) '(1 2 3) '(1 2 3)) '(3 6 9) "test mapcar-i 1")
(test (mapcar-i (lambda(x y z)(+ x y z)) '(1 2 3) '(1 2 3) '(1 2 3)) '(3 6 9) "test mapcar-i 2")
(test (mapcar + '(1 2 3) '(1 2 3) '(1 2 3)) '(3 6 9) "test mapcar 1")
(test (mapcar + '(1 2 3 4) '(1 2 3) '(1 2 3 4)) '(3 6 9) "test mapcar 1 bis") ; mapcar con liste di lunghezza diversa
(test (mapcar (lambda(x y z)(+ x y z)) '(1 2 3) '(1 2 3) '(1 2 3)) '(3 6 9) "test mapcar 2")
(test (mapcar  (lambda(x)(cons (car x)(reverse (remove (car x)(cdr x))))) '((a b c a b c)(b c d b c d)(c d e c d e)(d e f d e f))) '((a c b c b) (b d c d c) (c e d e d) (d f e f e)) "test di Alexander Burger")

(test (map (lambda(x)(+ x x)) '(1 2 3)) '(2 4 6) "test map 1")

(test (tc_t5 1 2 3) 6 "test closure tc_t5") ; tutti i parametri sono saturati, per cui funziona sia con dynamic che con lexical scoping

(test (assoc 'x (pairlis '(a b c) '(1 2 3) nil)) nil "test assoc-pairlis 1" )
(test (assoc 'x (pairlis '(a b x) '(1 2 3) nil)) '(x.3) "test assoc-pairlis 1" )

(test (sublis '((x.1)) '(x 2 3)) '(1 2 3) "test sublis 1" )

(test (fib 3) 3 "test fib(3)=3")
(test (fib 28) 514229 "test fib(28)=514229")

(test (sort '(b c a)) '(a b c) "(sort '(b c a))='(a b c)")
(test (sort '(2 3 1)) '(1 2 3) "(sort '(2 3 1))='(1 2 3)")

(test (let((j nil))(dolist(i '(1 2 3) j)(setq j i))) '3 "(let((j nil))(dolist(i '(1 2 3) j)(setq j i)))=3")
(test (dotimes(i 10 i)) 10 "(dotimes(i 10 i))=10")
(test (let((j 0))(dotimes(i 10 j)(setq j i))) 9 "(let((j 0))(dotimes(i 10 j)(setq j i)))=9")

(if (tail-call) (test (count-down 100000) 0 "(count-down 100000)=0") t)

(test (solve-maze 1 nil maze) '(6 7 8 5 2 1) "(solve-maze 1 nil maze)=(6 7 8 5 2 1)")

(test ((lambda(x . y)(list x y)) 1 2) '(1 (2)) "parametri catch-all 1")
(test ((lambda(x . y)(list x y)) 1) '(1 nil) "parametri catch-all 2")
(test ((lambda(x . y)(list x y)) 1 2 3) '(1 (2 3)) "parametri catch-all 3")
(test ((lambda x x) 1) '(1) "parametri catch-all 4")
(test ((lambda x x)) nil "parametri catch-all 4")


; (test 1 2 "prova di errore" )

)

