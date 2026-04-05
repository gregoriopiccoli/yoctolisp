; compila il corpo di una funzione ricevendo la lista delle variabili che sono state rinominate nella forma #<n>
(defun compile-body(l v cnt)(cond
  ((null l) nil)
  ((eq l 'lambda) :not-compilable)
  ((atom l)(let((p (assoc l v)))(if(null p) l (cdr p))))
  ((= 'let (car l))(compile-let l v cnt))
  (t(let(
      (p1 (compile-body(car l) v cnt))
      (p2 (compile-body(cdr l) v cnt)))
    (if(or(= p1 :not-compilable)(= p2 :not-compilable))
      :not-compilable
      (cons p1 p2)
    )))
))


(defun compile-let(let-expr v cnt)
  ; è una let, devo estendere v con i nomi che assegno alle variabili della let
  ;            devo compilare il corpo della let con la nuova tabella di associazioni (v)
  ;            devo compilare le assegnazioni che possono a loro volta contenere let e quindi far salire il contatore
  (let ((compiled-let-vars (compile-let-asgn (cadr let-expr) v cnt)))     
     (if (= :not-compilable compiled-let-vars) 
        :not-compilable
        (let ((compiled-let-body (compile-body (cddr let-expr) (append (make-let-assoc (cadr let-expr) compiled-let-vars) v) (+ cnt (len (cadr let-expr)))))) ; !!!!! <--- qui si deve aggiungere il numero giusto
           (if (= :not-compilable compiled-let-body)
              :not-compilable
              (cons 'let (cons compiled-let-vars compiled-let-body))
           )
        )
     )
  )        
)

(defun compile-let-asgn(let-vars v cnt)
  (if (null let-vars) 
     nil                                                       ; ricorsione, è arrivato alla fine della lista delle variabili
     (let((let-expr (compile-body (cdar let-vars) v cnt))      ; compila il corpo dell'assegnazione, attenzione che cambia cnt
          (new-cnt (+ cnt (count-let-vars (cdar let-vars))) )) ; calcola quante variabili sono già state usate dall'espressione di calcolo per l'assegnazione
        (if (= :not-compilable let-expr)
           :not-compilable
           (let((let-asgn-rest (compile-let-asgn (cdr let-vars) v new-cnt)))         ; riceve la compilata di quelli che seguono
              (if (= :not-compilable let-asgn-rest)
                 :not-compilable
                 (cons (cons (let-name let-vars new-cnt) let-expr) let-asgn-rest)    ; ricostruisce la lista delle variabili di let con i nuovi nomi
              )
           )
        )
     )          
  )   
)

(defun let-name(let-expr cnt) (n-name (+ cnt (len let-expr))))

; funzione che data la lista delle let prima e dopo la trasformazione crea la lista da mettere nelle associazioni
(defun make-let-assoc(let-before let-after)
  (if (null let-before)
    nil
    (cons (cons (caar let-before)(caar let-after)) (make-let-assoc (cdr let-before) (cdr let-after)))
  ) 
)

(defun o-compile-let(let-expr v cnt)
  (let ((let-body (compile-body (caddr let-expr) v cnt))
        (let-vars (compile-let-asgn (cadr let-expr) v cnt)))
   (progn
    ; DEBUG MSGS
    (princ "let:")(println let-expr)
    (princ "v=")(println v)  
    (princ "vars=")(println let-vars)  
    (princ "body=")(println let-body)  
    (if (= :not-compilable let-body) :not-compilable (list 'let let-vars let-body))
  ))  
)
  
(defun o-compile-let-asgn(let-vars v cnt)
  (if(null let-vars) 
    nil
   (let ((body (compile-body (cadar let-vars) v cnt)))
     (if (= body :not-compilable) 
       :not-compilable
       (cons (list (caar let-vars) body)(compile-let-asgn (cdr let-vars) v cnt))
))))  

; nel compilare il corpo della let c'è il problema dell' environment: prima si valutano le setq con v poi il corpo estendendo la lista delle associazioni

 
; compila la definizione di funzione
(defun compile-fun(f)(let(
    (vararg (is-var-args (cadr f)))
    (args   (flatten-args (cadr f)))
    (nlet   (count-let-vars (caddr f)))
  )      
  (cond
    ((<> (car f) 'lambda) :not-compilable)
    ((> (+ (len args) nlet) 26) :not-compilable) ; si possono avere fino a 26 variabili nello stack, parametri e let (per ora, poi vediamo se espandere la sintassi #)
    (t (make-compiled-fun (args-num args vararg) nlet (compile-body (caddr f)(mk-assoc args 0) (len args)) (cdddr f))))
))

(defun make-compiled-fun(nargs nlet body closure)(if(= body :not-compilable) :not-compilable (cons '#lambda (cons (cons nargs nlet) (cons body closure)))))

; IS-VAR-ARGS: controlla se ha un numero fisso di parametri o se è del tipo f(x y . z) che cattura in z tutti i parametri oltre x e y
(defun is-var-args(l)(if(atom l) t (let((ll (last l)))(not(null (cdr ll)))))) 
; FLATTEN-ARGS:
(defun flatten-args(l) (if (is-var-args l) (flatten-args-2 l) l))
(defun flatten-args-2(l) (if (atom l) (cons l nil) (cons (car l)(flatten-args-2 (cdr l)))))
(defun args-num(args vararg)(* (len args) (if vararg -1 1)))
 
(defun mk-assoc(l n)(if(null l)nil(cons(cons (car l) (n-name n))(mk-assoc (cdr l)(+ n 1)))))

(defun n-name(n)(nth n '(#A #B #C #D #E #F #G #H #I #J #K #L #M #N #O #P #Q #R #S #T #U #V #W #X #Y #Z)))

; torna il numero di variabili da riservare nello stack per tutte le let presenti nel corpo della funzione
(defun count-let-vars(body)(cond
  ((atom body) 0)
  ((eq 'let (car body)) (+ (count-let-vars-list (cadr body)) (count-let-vars(cddr body))) )
  (t (+ (count-let-vars(car body)) (count-let-vars (cdr body))))
))

(defun count-let-vars-list(vlist)(cond
  ((null vlist) 0)
  (t (+ 1 (count-let-vars (cdar vlist)) (count-let-vars-list (cdr vlist))))
))

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



