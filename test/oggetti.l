; -- definisce l' operazione "esplora"
(defun ->(obj name)
   (let ((res (cdr(assoc name obj))))
      (cond
        ((atom res) res)
        ((eq (car res) 'lambda)(append (list 'lambda (cadr res)(caddr res)) obj))
        (t res)
)))

; -- aggiorno una proprietà esistente in un oggetto
(defun =>(obj name value)
   (let((p (assoc name obj)))
      (if (null p)
         nil
         (rplacd p value)
)))

; tutto sta in piedi per il sistema che ho fatto per gestire le closure
; di fatto l' operazione -> chiude le funzioni sugli oggetti da cui partono

(defun clone-obj(x)
  (if (null x)
     nil
     (cons (cons (caar x)(cdar x))(clone-obj(cdr x)))
))

; --- toglie l' ambiente ad una closure
(defun open-cl(f)
  (list 'lambda (cadr f) (caddr f))
)
; --- associa l' ambiente ad una funzione creando una closure
(defun make-cl(f e)
  (cons 'lambda (cons (cadr f) (cons (caddr f) e)))
)
