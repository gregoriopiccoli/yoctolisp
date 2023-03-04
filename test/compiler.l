; compila il corpo di una funzione ricevendo la lista dei parametri con l' associazione ad un comando #<n>
(defun compile-body(l v)(cond
  ((null l) nil)
  ((eq l 'lambda) :not-compilable)
  ((atom l)(let((p (assoc l v)))(if(null p) l (cdr p))))
  ((= 'let (car l))(compile-let l v))
  (t(let(
      (p1 (compile-body(car l) v))
      (p2 (compile-body(cdr l) v)))
    (if(or(= p1 :not-compilable)(= p2 :not-compilable))
      :not-compilable
      (cons p1 p2)
    )))
))

(defun compile-let(let-expr v)
  (let ((let-body (compile-body (caddr let-expr) v))
        (let-vars (compile-let-asgn (cadr let-expr) v)))
   (progn
    ; DEBUG MSGS
    ;(princ "let:")(println let-expr)
    ;(princ "v=")(println v)  
    ;(princ "vars=")(println let-vars)  
    ;(princ "body=")(println let-body)  
    (if (= :not-compilable let-body) :not-compilable (list 'let let-vars let-body))
  ))  
)
  
(defun compile-let-asgn(let-vars v)
  (if(null let-vars) 
    nil
   (let ((body (compile-body (cadar let-vars) v)))
     (if (= body :not-compilable) 
       :not-compilable
       (cons (list (caar let-vars) body)(compile-let-asgn (cdr let-vars) v))
))))  

; nel compilare il corpo della let c'è il problema dell' environment: prima si valutano le setq con v poi il corpo estendendo la lista delle associazioni

 
; compila la definizione di funzione
(defun compile-fun(f)(let(
    (vararg (is-var-args (cadr f)))
    (args   (flatten-args (cadr f))))  
  (cond
    ((<> (car f) 'lambda) :not-compilable)
    ((> (len args) 20) :not-compilable)
    (t(make-compiled-fun (args-num args vararg)(compile-body (caddr f)(mk-assoc args 0)) (cdddr f))))
))

(defun make-compiled-fun(n body closure)(if(= body :not-compilable) :not-compilable (cons '#lambda (cons (cons n (max-let-vars body 0)) (cons body closure)))))

; IS-VAR-ARGS: controlla se ha un numero fisso di paramertri o se sono varianti
(defun is-var-args(l)(if(atom l) t (let((ll (last l)))(not(null (cdr ll)))))) 
; FLATTEN-ARGS:
(defun flatten-args(l) (if (is-var-args l) (flatten-args-2 l) l))
(defun flatten-args-2(l) (if (atom l) (cons l nil) (cons (car l)(flatten-args-2 (cdr l)))))
(defun args-num(args vararg)(* (len args) (if vararg -1 1)))
 
(defun mk-assoc(l n)(if(null l)nil(cons(cons (car l) (nth n '(#A #B #C #D #E #F #G #H #I #J #K #L #M #N #O #P #Q #R #S #T #U #V #W #X #Y #Z)))(mk-assoc (cdr l)(+ n 1)))))

; torna il numero di variabili da riservare nello stack per tutte le let presenti nel corpo della funzione
(defun max-let-vars(body n) n) ; da fare!

; compila una funzione assegnata ad un nome
(defun compile(fn)(let((c (compile-fun (eval fn))))(if(= c :not-compilable) :not-compilable (set fn c))))

; --- compila il benchmark
(defun cbe()(progn
  (compile 'fib)
  (compile 'map-i)
  (compile 'unify)
  (compile 'matchvar)
  (compile 'varp)
  (compile 'sort)
  (compile 'sort-h2)
  (compile 'occursp)
))



