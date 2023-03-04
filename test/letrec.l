(defun t1()
  (let((a 100)
       (b 10)
       (f (lambda(x)(+ a x)))) ; la funzione viene chiusa nel' ambiente globale, giusto per la specifica della LET
  f) ; torna (lambda(x)(+ a x)) chiusa sull' ambiente globale
)

(defun t2()
  (let((a 100)
       (b 10))
  (lambda(x)(+ a x))) ; torna (lambda(x)(+ a x)) chiusa nell' ambiente della LET
)

(defun t3()
  (let((a 100)
       (b 10)
       (f (lambda(x)(+ a x)))) ; la funzione viene chiusa nel' ambiente globale, giusto per la specifica della LET
  (f b)) ; da errore perché f è chiusa nell' ambiente globale e quindi non vede a!
)

; --- COME POSSO RIUSCIRE A CHIUDERE NELLA LET? COME POSSO DEFINIRE DELLE FUNZIONI LOCALI?

(defun t4()
  (let((a 100)
       (b 10))
    (let((f (lambda(x)(+ x a)))) ; con questo seconda LET chiudo la funzione nell' ambiente dove sono definite le variabili a e b
    f)
  )
)

(defun t5()
  (let((a 100)
       (b 10))
    (let((f (lambda(x)(+ x a)))
         (g (lambda(x)(+ x b)))) ; con questo seconda LET chiudo la funzione nell' ambiente dove sono definite le variabili a e b
    (f (g 1)))
  )
)

(defun t6()
  (let((a 100)
       (b 10)
       (f (lambda(x)(+ x a)))
       (g (lambda(x)(+ x b)))) ; ora F e G sono nella let, ma chiuse sull' ambiente globale
  (eval f)) ; cosi F viene chiusa sull' ambiente della LET
)

(defun t7()
  (let((a 100)
       (b 10)
       (f (lambda(x)((eval g)(+ x a))))
       (g (lambda(x)(+ x b)))) ; ora F e G sono nella let, ma chiuse sull' ambiente globale
  ((eval f) 1)) ; cosi F e G sono chiuse sull' ambiente della LET e poi chiamate
)

(defun t8()
  (let((a 100)
       (b 10)
       (f (lambda(x)(g(+ x a))))
       (g (lambda(x)(+ x b)))) ; ora F e G sono nella let, ma chiuse sull' ambiente globale
  (progn
     (setq f (eval f))
     (setq g (eval g))
     (f 1)
  )) ; cosi F e G sono chiuse sull' ambiente della LET e poi chiamate
)

(defun t9()
  (let((a 100)
       (b 10)
       (f (lambda(x)(g(+ x a))))
       (g (lambda(x)(+ x b)))) ; ora F e G sono nella let, ma chiuse sull' ambiente globale
  (closing (f g)
     (f (g 1))
  )) ; cosi F e G sono chiuse sull' ambiente della LET e poi chiamate
)

(defmacro closing(funcs body)(cons 'progn (append (map (lambda(x)(list 'setq x (list 'eval x))) funcs) (cons body nil))))

;
; ALLA FINE HO IMPLEMENTATO LA MACRO "labels" DEL COMMON LISP CHE E' DAVVERO COMODA!
;
