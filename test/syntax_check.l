; --- let
(let ((x 1)(y 1)) (= x y))
(let (x y z) (null x))

; --- named let 
(let loop ((x 0))(if (= x 10) t (loop (+ x 1))))
(let lo1 ((x 0))(let lo2 ((y 0)) (if (= x 3) t (if (= y 3) (lo1 (+ x 1)) (lo2 (println (+ y 1)))))))

; --- labels
(labels ((f1(x)(f2 (+ x 1)))(f2(x)(= x 2)))(f1 1))

; --- do
(do((x 1 (+ x 1)))
   ((= x 10) t)
)
	 
(do((x 1 (+ x 1)))
   ((= x 10) t)
	 100 ; -- eventuale corpo del ciclo, non 'cè quasi mai ...
)

; --- while
(let ((x 0))(while (< x 10) (setq x (+ x 1)) t))
(let ((x 0))(while (< x 10) (setq x (+ x 1))  ))
 
; --- dotimes
(dotimes (i 5) (print i))

; --- dolist 
(dolist (i '(1 2 3 4 5)) (print i))

; --- if 
(if (= 1 1) t nil)
(if (= 2 1) nil t)
(if (= 1 1) t)
