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

; -- funzioni usate dalla seconda suite --
(defun tf1 (x) (* x 2))
(defun tf2 (x y) (+ x y))
(defun tf3 (x . r) (cons x r))
(defun tf5 x x)
(defun counter (n) (let ((c 0)) (lambda () (setq c (+ c n)) c)))

; -- seconda suite: operatori, stringhe, liste e controllo --
;    aggiunta per coprire le zone che non erano testate, in particolare gli operatori con
;    piu' di due argomenti e gli argomenti misti: i valori attesi sono quelli ricavati
;    dall'implementazione di riferimento.
(test-suite "-- Operatori, stringhe, liste e controllo --"

; --- aritmetica: un solo argomento ---
(test (+ 1) 1 "un argomento (+ 1)")
(test (- 1) -1 "un argomento (- 1)")
(test (* 1) 1 "un argomento (* 1)")
(test (/ 1) 1 "un argomento (/ 1)")
(test (% 1) 1 "un argomento (% 1)")
(test (^ 1) 1 "un argomento (^ 1)")
(test (- 5) -5 "un argomento (- 5)")

; --- aritmetica: piu' argomenti valutati da sinistra a destra ---
;     solo il resto dipende davvero dall'ordine, ((a%b)%c) != ((a%c)%b): la divisione
;     intera e la potenza sono componibili, quindi per "/" e "^" questi test
;     controllano il risultato e non l'ordine.
(test (+ 1 2) 3 "(+ 1 2)")
(test (- 1 2) -1 "(- 1 2)")
(test (* 3 4) 12 "(* 3 4)")
(test (/ 7 2) 3 "(/ 7 2)")
(test (% 7 2) 1 "(% 7 2)")
(test (^ 2 10) 1024 "(^ 2 10)")

(test (+ 1 2 3 4 5 6 7 8 9 10) 55 "(+ 1 2 3 4 5 6 7 8 9 10)")
(test (- 100 1 2 3 4 5 6 7 8 9) 55 "(- 100 1 2 3 4 5 6 7 8 9): ordine degli argomenti")
(test (- 5 1 1 1) 2 "(- 5 1 1 1): ordine degli argomenti")
(test (- 5 1 2) 2 "(- 5 1 2): ordine degli argomenti")
(test (* 2 3 4 5 6 7 8 9 10) 3628800 "(* 2 3 4 5 6 7 8 9 10)")
(test (/ 100 5 2) 10 "(/ 100 5 2) con piu' argomenti")
(test (/ 100 2 5) 10 "(/ 100 2 5) con piu' argomenti")
(test (/ 7 2 3) 1 "(/ 7 2 3) con piu' argomenti")
(test (/ 1 2 4 8) 0 "(/ 1 2 4 8) con piu' argomenti")
(test (/ 1000000 7 3 5 11) 865 "(/ 1000000 7 3 5 11) con piu' argomenti")
(test (% 100 5 3) 0 "(% 100 5 3): ordine degli argomenti")
(test (% 7 2 5) 1 "(% 7 2 5): ordine degli argomenti")
(test (% 7 3 5) 1 "(% 7 3 5): ordine degli argomenti")
(test (% 7 5 2) 0 "(% 7 5 2): ordine degli argomenti")
(test (% 7 2 3 5) 1 "(% 7 2 3 5): ordine degli argomenti")
(test (% 13 4 5 6) 1 "(% 13 4 5 6): ordine degli argomenti")
(test (% 100 7 3) 2 "(% 100 7 3)")
(test (% 1000 3 7) 1 "(% 1000 3 7)")
(test (% 1000 7 3 5 11) 0 "(% 1000 7 3 5 11) con piu' argomenti")
(test (% 7 2 3) 1 "(% 7 2 3): ordine degli argomenti")
(test (% 1000000 7 3 5 11) 1 "(% 1000000 7 3 5 11) con piu' argomenti")
(test (^ 2 3 2) 64 "(^ 2 3 2) con piu' argomenti")
(test (^ 3 2 3) 729 "(^ 3 2 3) con piu' argomenti")
(test (^ 2 3 2 2 2) 16777216 "(^ 2 3 2 2 2) con piu' argomenti")

; --- aritmetica: segni ---
(test (list (+ -1 -2) (- -1 -2) (* -1 -2) (/ -7 2) (% -7 2) (/ 7 -2) (% 7 -2)) '(-3 1 2 -3 -1 -3 1) "aritmetica con numeri negativi")
(test (list (^ 2 0) (^ 0 0) (^ -2 3) (^ 2 30)) '(1 1 -8 1073741824) "potenze")

; --- stringhe ---
(test (+ "a" "b" 1 "c" 2) "ab1c2" "(+ ...) con stringhe, numeri e simboli")
(test (+ "x" 1 'y "z" 'w) "x1yzw" "(+ ...) che parte da una stringa")
(test (+ 'a 'b 1) "ab1" "(+ ...) che parte da un simbolo")
(test (+ (+ "x" "y") "z") "xyz" "(+ ...) annidato")
(test (+ "abc") "abc" "(+ abc)")
(test (list (len (spaces 5)) (len "ciao") (len '(1 2 3)) (len nil)) '(5 4 3 0) "len")
(test (list (substr "abcdef" 2) (substr "abcdef" 2 3)) '("cdef" "cde") "substr")
(test (list (at "cd" "abcdef") (at "zz" "abcdef") (at "a" "a")) '(2 nil 0) "at")

; --- confronti ---
(test (list (<> 1 1) (<> 1 2)) '(nil t) "<>")
(test (list (< 1 "a") (< "a" 1) (< 'a 1) (< 1 'a)) '(nil nil nil nil) "confronto fra tipi diversi: nil")

; --- liste ---
(test (list (car nil) (cdr nil) (car '(1 2)) (cdr '(1 2)) (car (cdr '(1 2 3)))) '(nil nil 1 (2) 2) "car e cdr")
(test (list (list) (list 1) (list 1 2 3) (list* 1) (list* 1 2 3)) '(nil (1) (1 2 3) 1 (1 2 . 3)) "list e list*")
(test (list (append '(1 2) '(3 4)) (append nil '(1)) (append '(1) nil) (append) (reverse '(1 2 3)) (reverse nil)) '((1 2 3 4) (1) (1) nil (3 2 1) nil) "append e reverse")
(test (list (remove 2 '(1 2 3 2)) (remove 9 '(1 2))) '((1 3) (1 2)) "remove")
(test (list (nth 1 '(a b c)) (nth 0 nil) (member 'b '(a b c)) (member 'z '(a b c))) '(b nil (b c) nil) "nth e member")
(test (list (assoc 'b '((a 1)(b 2))) (assoc 'z '((a 1)))) '((b 2) nil) "assoc")
(test (list (equal '(1 2) '(1 2)) (equal "a" "a") (equal '(1) '(2)) (eq 'a 'a) (eq 1 1) (eq "a" "b")) '(t t nil t t nil) "equal ed eq")

; --- predicati ---
(test (list (nump 1) (nump "a") (strp "a") (strp 1) (symp 'a) (symp :k) (symp 1) (hashsymp '#A) (hashsymp 'a) (atom 1) (atom '(1)) (null nil) (null 0) (not nil) (not 0)) '(t nil t nil t t nil t nil t nil t nil t nil) "nump strp symp hashsymp atom null not")
(test (list (celltype 1) (celltype "a") (celltype 'a) (celltype '(1)) (celltype nil)) '(3 4 1 0 nil) "celltype")

; --- eval e apply ---
(test (list (eval '(+ 1 2)) (eval '(+ 1 2) nil) (apply + '(1 2 3)) (apply '+ '(1 2 3)) (eval (list '+ 1 2))) '(3 3 6 6 3) "eval e apply")

; --- costrutti di controllo ---
(test (list (if t 1 2) (if nil 1 2) (if nil 1) (if t 1) (if 0 1 2) (if nil nil 2)) '(1 2 nil 1 1 2) "if")
(test (list (cond (nil 1) (t 2)) (cond (nil 1)) (cond (else 3)) (cond) (cond (1 5) (t 6))) '(2 nil 3 nil 5) "cond")
(test (list (and 1 2 3) (and) (and 1 nil 3) (or nil 2) (or) (or nil nil) (or nil 1 2)) '(3 t nil 2 nil nil 1) "and e or")
(test (list (progn 1 2 3) (prog1 1 2 3) (progn) (prog1 5)) '(3 1 nil 5) "progn e prog1")
(test (list (let ((x 1)(y 2)) (+ x y)) (let (x y) (list x y)) (let ((x 1)) (let ((x 2)) x))) '(3 (nil nil) 2) "let")
(test (let loop ((i 0)(acc nil)) (if (= i 4) acc (loop (+ i 1) (cons i acc)))) '(3 2 1 0) "named let")
(test (list (do ((i 0 (+ i 1)) (s 0 (+ s i))) ((= i 5) s)) (do ((i 0 (+ i 1)) (s 0)) ((= i 3) (list i s))) (do ((i 0 (+ i 1))) ((= i 3) 'x))) '(10 (3 0) x) "do")
(test (list (dotimes (i 4) i) (dolist (i '(1 2 3)) i) (dotimes (i 0 'z))) '(nil nil z) "dotimes e dolist")

; --- funzioni, parametri e chiusure ---
(test (list (tf1 21) (tf2 1 2) (tf3 1 2 3) (tf3 1) (tf5 9)) '(42 3 (1 2 3) (1) (9)) "parametri normali, dotted e duplicati")
(test (((lambda (x) (lambda (y) (+ x y))) 10) 5) 15 "chiusura")
(test ((label lbl (lambda (n) (if (= n 0) 'z (lbl (- n 1))))) 5) 'z "label ricorsivo")
(test (list (map (lambda (x) (* x x)) '(1 2 3)) (mapcar + '(1 2 3) '(4 5 6)) (filter (lambda (x) (> x 1)) '(1 2 3)) (filter (lambda (x) (> x 9)) '(1 2 3))) '((1 4 9) (5 7 9) (2 3) nil) "map mapcar filter")
(setq tfv (list 1 2 3))
(setq cc (counter 5))
(test (list (cc) (cc) (cc)) '(5 10 15) "chiusura con stato")

; --- lettore ---
(test (list +5 -3 007 -0 0 12) '(5 -3 7 0 0 12) "numeri con segno, zeri iniziali e senza segno")
(test (list (nump +5) (nump -3) (nump 12) (nump 'abc) (nump "a")) '(t t t nil nil) "nump sui numeri letti dal lettore")
(test (list 'nil nil '() () 'a) '(nil nil nil nil a) "nil come vuoto e come simbolo")

)

