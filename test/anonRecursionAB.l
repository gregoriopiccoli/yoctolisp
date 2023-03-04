; --- ricorsione anonima come proposta da Alexander Burger per Picolisp
; --- si riesce a fare anche senza le stranezze di Picolisp, sia in una versione "pulita" ma lenta che assemblando la closure con velocità più elevata
(defmacro recur(args body)(let ((f (list 'lambda args body (cons 'recurse 1000)))) (progn (rplacd (cadddr f) f) (list 'quote f))))
(defmacro recur-pulita(args body)(list 'quote (list 'lambda args (list 'let (list (list 'recurse (list 'recur-pulita args body))) body)))) ; --- versione "pulita" ma molto più lenta!

((recur(x)(if (= x 1) 1 (* x (recurse (- x 1))))) 5) ; --- fattoriale con ricorsione anonima

(time(dotimes(i 1000000)((recur(x)(if(= x 1) 1 (* x (recurse (- x 1))))) 5)))        ; --- 1000000 di fattoriale (anonimo) di 5,  875 millisecondi 
(time(dotimes(i 1000000)((recur-pulita(x)(if(= x 1) 1 (* x (recurse (- x 1))))) 5))) ; --- 1000000 di fattoriale (anonimo) di 5, 2703 millisecondi
