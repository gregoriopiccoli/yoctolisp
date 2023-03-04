; ---- prova oggetti
; @ accede o setta i valori agli oggetti
;

(defun @(o n . v) 
  (if (null v)
     (cdr(assoc n o))                 ; è una lettura, cerca il valore nella property list
	 (let((p (assoc n o)))
	   (if (null p) 
	       nil                                   ; non c'è il simbolo nella lista, non fa nulla
		   (cdr(rplacd p (make-cl (car v) o)))   ; sostituisce il valore nella lista
		)
	 )
  )
)

; --- associa l' ambiente ad una funzione creando una closure
(defun make-cl(f e)
  (cond 
    ((atom f) f)
    ((eq (car f) 'lambda)(cons 'lambda (cons (cadr f) (cons (caddr f) e))))
	(t f)
  )
)

(setq oo '((x . 1)(y . 10)(f . nil)))
(@ oo 'x)     ; -> 1
(@ oo 'y)     ; -> 10
(@ oo 'x 100) ; -> 100 e modificato oo
(@ oo 'x)     ; -> 100
(@ oo 'f '(lambda(z)(+ x y z))) ; f viene settata alla funzione chiusa sull'oggetto!
((@ oo 'f) 1) , -> 111

