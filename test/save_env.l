; funzioni per salvare l'environment o una lista di definizioni in un file

; salva lo stato dell'interprete in un file
(defun save-env(fn)(progn (output fn) (print-env (env)) (output nil)))

; salva una lista di definizioni in un file
(defun save-defs(fn defs)(progn (output fn) (print-env (mk-env-from-defs defs)) (output nil)))

(defun mk-env-from-defs(defs)(if (null defs) nil (cons (cons (car defs)(eval (car defs))) (mk-env-from-defs (cdr defs)) )))

(defun print-env(e)(if (null e) t (progn (print-env-elem (car e)) (print-env (cdr e)))))

(defun print-env-elem(e)(cond
  ;((atom (cdr e)) (println (list 'setq (car e) (list 'quote (cdr e)))))
  ((atom (cdr e)) (println (list 'setq (car e) (if (symp (cdr e)) (list 'quote (cdr e)) (cdr e)) )))
  ((eq (cadr e) lambda) (print-lam-mac e))
  ((eq (cadr e)  macro) (print-lam-mac e)) 
  (t (println (list 'setq (car e) (list 'quote (cdr e)))))
))

; stampa una lambda o una macro, se c'è la closure è una setq altrimenti una defun/defmacro
(defun print-lam-mac(e)(let (
      (typ (cadr e))
      (clo (cddddr e))
   )
   (cond 
     ((atom clo) (println (list (if (eq typ lambda) 'defun 'defmacro) (car e) (caddr e) (cadddr e))))
     (t (println (list 'setq (car e) (list 'quote (cdr e)))))
)))
       
