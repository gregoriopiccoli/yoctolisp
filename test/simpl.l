(load "match.l")

;
; --- funzione che cerca la regola da applicare e la applica, finché non ci sono più regole
;
(defun Simpl(exp rules)
  (do((e exp                        (Simpl-ApplyRule e r rules)) ; all' inizio è l' espressione passata, poi applica la regola trovata nel giro precedente
      (r (Simpl-PickRule exp rules) (Simpl-PickRule e rules)))   ; cerca la regola da applicare all' espressione corrente
    ((null r)(Simpl-ApplyEndRule e rules))                  ; non sono state trovate regole applicabili ... termina
   
  )
)

(defun FullSimpl(exp rules)(Simpl(FullSimpl-1 exp rules) rules)) ; prima semplifica ogni elemento dell' espressione, poi semplifica l' espressione stessa

(defun FullSimpl-1(exp rules)(cond
  ((atom exp) exp)
  ((listp(car exp))(cons (Simpl (FullSimpl-1 (car exp) rules) rules)(FullSimpl-1 (cdr exp) rules)))
  (t(cons(car exp)(FullSimpl-1 (cdr exp) rules)))
))

; --- trova la prossima regola da applicare, nil se non la trova, (rule.match) se trova una regola che matcha l' espressione
(defun Simpl-PickRule(exp rules)
  (if (null rules)
     nil
     (let((m (Match (Simpl-MatchPart (car rules)) exp)))
        (if (eq m :failed)
          (Simpl-PickRule exp (cdr rules))
          (cons(car rules) m)
     ))
))

; applica una regola: riceve l' espressione e la cons (rule.match)
(defun Simpl-ApplyRule(exp r rules)(progn
  ;(princln " --apply --")
  ;(princln "exp:" exp)
  ;(princln "rule name:" (caar r))
  ;(princln "template:" (caddar r))
  ;(princln "calculations:" (cadddar r))
  ;(princln "match-list:" (cdr r))
  (princln "firing rule " (caar r) " on " exp " --> "
  (let((match-list (cdr r))
       (rule-template (caddar r))
       (rule-calculations (cadddar r)))
        ; --- esegue la regola di trasformazione!
    (Simpl-RewriteMatch rule-template (Simpl-AddCalculations rule-calculations match-list))
))))

; applica la regola finale all' espressione (se esiste), altrimenti ritorna l' espressione così com'è
(defun Simpl-ApplyEndRule(exp rules)
   (let((end-rule (assoc 'at-end rules)))            ; verifica se c'è una regola finale
      (if (null end-rule) 
         exp 
         (progn 
           (princln "firing end rule " (car end-rule) " on " exp " --> "
           ((caddr end-rule)exp)) ; e in caso la applica
))))

(defun Simpl-RewriteMatch(e m)
  (if (atom e)
    (let ((a (assoc e m))) 
       (cond 
          ((null a) e)
          ((Match-Varp e) (cdr a))
          ;((Match-Seqp e) (cdr a))
          (t (error "Simpl-RewriteMatch e1"))))          
    (let((a (assoc (car e) m)))
       (cond
         ((null a)(cons (Simpl-RewriteMatch (car e) m) (Simpl-RewriteMatch (cdr e) m)))
         ((Match-Varp (car a)) (cons (cdr a) (Simpl-RewriteMatch (cdr e) m)))
         ((Match-Seqp (car a)) (if (null (cdr a)) (Simpl-RewriteMatch (cdr e) m) (append (cdr a) (Simpl-RewriteMatch (cdr e) m))))
         (t (error "Simpl-RewriteMatch e2"))))          
))

; --- riceve la lista di nuove variabili da calcolare e le deve aggiungere a quelle già rilevate duerante il match 
;     l' ambiente di valutazione dell' espressione è la lista stessa
(defun Simpl-AddCalculations(c l)(cond
  ((null c) l)
  (t(Simpl-AddCalculations(cdr c)(cons (cons (caar c) (eval (cadar c) l)) l)))
))

(defun Simpl-MatchPart(rule)(cadr rule))

; ------------------------------------------------------------------------------------------------------------------------------------------------------
;
; Sistema di regole per semplificare le espressioni matematiche
;

(defun se(exp)(FullSimpl exp arith-rules))

(defun notnump(x)(not(nump x)))
(defun notzerop(x)(<> x 0))

(defun sort-arith-ops(l)(cond
  ((atom l) l)
  ((=(car l) '+) (cons '+ (sort (cdr l))))
  ((=(car l) '-) (cons '- (cons(cadr l)(sort(cddr l)))))
  ((=(car l) '*) (cons '* (sort (cdr l))))
  ((=(car l) '/) (cons '/ (cons(cadr l)(sort(cddr l)))))
  (t l)
))

(setq arith-rules '(

  ; --- regole per la somma
  (add-0      (+ *h 0 *t)                                      (+ *h *t)                 nil )
  (add-0term  (+)                                              0                         nil )
  (add-1term  (+ ?x)                                           ?x                        nil )
  (add-2num   (+ *h1 (?x nump) *h2 (?y nump) *t)               (+ *h1 ?new *h2 *t)       ((?new (+ ?x ?y))) )
  (add-sub+   (+ *h (+ *l) *t)                                 (+ *h *l *t)              nil)
  (add-sub0   (+ *h (- ?x) *t)                                 (+ *h ?x *t)              nil )
  (add-sub1   (+ *h (- ?x (?y nump)) *t)                       (+ *h ?x ?new *t)         ((?new (- 0 ?y))) )
  (add-uminsl (+ *h1 ?x *h2 (- ?y ?x) *h3)                     (+ *h1 *h2 ?y *h3)        nil ) ; serve molto su trasformazione di (- y .. x ..) in (+  y ... (- 0 x) ...)
  (add-uminsr (+ *h1 (- ?y ?x) *h2 ?x *h3)                     (+ *h1 *h2 ?y *h3)        nil ) ; questo va come sopra ...
  ; -- questa regola smonta la sottrazione nella divisione, ma lascia molti "unary minus" ...
  (add-sub-   (+ *h (- (?x notzerop) *ts) *t)             (+ *h ?x (- 0 *ts) *t) nil )
  ; -- questa invece semplifica solo se ci sono 3 termini ... ma è un pò sciocca ..
  ;(add-sub-   (+ *h (- ?x ?y ?z *ts) *t)                       (+ *h (- ?x *ts)(- 0 ?y)(- 0 ?z) *t) nil )
  ;(add-sub2   (+ *h (- ?x ?y) *m (- ?y ?z) *t) 
  (add-2sym   (+ *h1 ?x *h2 ?x *t)                             (+ *h1 ?new *h2 *t)       ((?new (se (list '* 2 ?x)))) )
  (add-subsym (+ *h1 (* (?y nump) ?x) *h2 ?x *t)               (+ *h1 ?new *h2 *t)       ((?new (se (list '* (+ ?y 1) ?x)))) )
  (add-subsym (+ *h1 ?x *h2 (* (?y nump) ?x) *t)               (+ *h1 ?new *h2 *t)       ((?new (se (list '* (+ ?y 1) ?x)))) )
  (add-subsym (+ *h1 (* (?y nump) ?x) *h2 (* (?z nump) ?x) *t) (+ *h1 ?new *h2 *t)       ((?new (se (list '* (+ ?y ?z)?x)))) )
  (add-subsym (+ *h1 (* (?y nump) ?x) *h2 (- 0 (* (?z nump) ?x)) *t) (+ *h1 ?new *h2 *t) ((?new (se (list '* (- ?y ?z) ?x)))) )
  (add-subsym (+ *h1 (- 0 (* (?y nump) ?x)) *h2 (* (?z nump) ?x) *t) (+ *h1 ?new *h2 *t) ((?new (se (list '* (- ?z ?y) ?x)))) )

  ; --- regole per la differenza
  (sub-0term  (-)                                              0                         nil )
  (sub-1term  (- ?x)                                           ?x                        nil )
  (sub-0      (- ?x *h 0 *t)                                   (- ?x *h *t)              nil )
  (sub-00     (- 0 (- 0 ?y))                                   ?y                        nil )
  (sub-sub    (- ?x *h (- ?y *m) *t)                           (- (+ ?x *m) *h ?y *t)    nil )
  (sub-1num   (- (?x nump) *h2 (?y nump) *t)                   (- ?new *h2 *t)           ((?new (- ?x ?y))) )
  (sub-2num   (- ?z *h1 (?x nump) *h2 (?y nump) *t)            (- ?z *h1 ?new *h2 *t)    ((?new (+ ?x ?y))) )
  (sub-1sym   (- ?x *h1 ?x *h2)                                (- 0 *h1 *h2)             nil )
  (sub-mult   (- ?x *h (* (?y nump) ?x) *t)                    (- 0 *h ?new *t)          ((?new (se (list '* (- ?y 1) ?x)))) )
  (sub-add    (- ?x *h (+ *a) *t )                             (- ?x *h *a *t)           nil )
  (sub-addm   (- (+ *hm (?x symp) *tm) *h (?x symp) *t)        (- ?new *h *t)            ((?new (se (cons '+ (append *hm *tm))))) )
  (sub-mulm   (- (* (?y nump) (?x symp)) *h (?x symp) *t)      (- ?new *h *t)            ((?new (se (list '* (- ?y 1) ?x)))) )
  (sub-add    (- (+ *h) ?y)                                    (+ *h ?new)               ((?new (se (list '- 0 ?y)))) )
  (sub-add2   (- (+ *h) ?y ?z *t)                              (- ?new ?z *t)            ((?new (se (cons '+ (append *h (cons (list '- 0 ?y) nil) ))))) )
  (sub-dist   (- (- ?x *h) *t)                                 (- ?x *h *t)              nil )

  ; --- regole per la moltiplicazione
  (mult-0     (* *h 0 *t)                                      0                         nil )
  (mult-0term (*)                                              1                         nil )
  (mult-1     (* *h 1 *t)                                      (* *h *t)                 nil )
  (mult--1    (* -1 ?x)                                        (- 0 ?x)                  nil )
  (mult-1term (* ?x)                                           ?x                        nil )
  (mult-2num  (* *h1 (?x nump) *h2 (?y nump) *t)               (* *h1 ?new *h2 *t)       ((?new (* ?x ?y))) )
  (mult-neg   (* *h1 (?y nump) *h2 (- 0 ?x) *t)                (* *h1 ?new *h2 ?x *t)    ((?new (- 0 ?y))) )
  (mult-neg   (* *h1 (- 0 ?x) *h2 (?y nump) *t)                (* *h1 ?x *h2 ?new *t)    ((?new (- 0 ?y))) )
  (mult-ord   (* (?x notnump) (?y nump) *t)                    (* ?y ?x *t)              nil )
  (mul-sub*   (* *h (* *l) *t)                                 (* *h *l *t)              nil )
  (mul-dis    (* ?x *h (+ ?y ?z) *t)                           (* *h ?new *t)            ((?new (se (list '+ (list '* ?x ?y)(list '* ?x ?z))))) )
  (mul-dis2   (* *h (+ ?y ?z) ?x *t)                           (* *h ?new *t)            ((?new (se (list '+ (list '* ?x ?y)(list '* ?x ?z))))) )
  (mul-dis3   (* ?x *h (- ?y ?z) *t)                           (* *h ?new *t)            ((?new (se (list '- (list '* ?x ?y)(list '* ?x ?z))))) ) 
  (mul-dis4   (* *h (- ?y ?z) ?x *t)                           (* *h ?new *t)            ((?new (se (list '- (list '* ?x ?y)(list '* ?x ?z))))) )
  
  ; --- regole per la divisione
  (div-0      (/ ?x *h 0 *t)                                   :div0                     nil )
  (div-1      (/ ?x *h 1 *t)                                   (/ ?x *h *t)              nil )
  (div-1term  (/ ?x)                                           ?x                        nil )
  (div-self   (/ ?x *h ?x *t)                                  (/ 1 *h *t)               nil )

  ; --- regole per l' esponenziazione 
  (exp-0      (^ 0 ?x)                                         0                         nil )
  (exp-0bis   (^ ?x 0)                                         1                         nil )
  (exp-0ter   (^ ?x 1)                                         ?x                        nil )
  (exp0-qua   (^ (?x nump)(?y nump))                           ?new                      ((?new (^ ?x ?y))) )
  (exp-1      (* *h ?x *m ?x *t)                               (* *h (^ ?x 2) *m *t)     nil )
  (exp-2      (* *h (^ ?x (?n nump)) *m ?x *t)                 (* *h (^ ?x ?new) *m *t)  ((?new (+ ?n 1))) )
  (exp-2bis   (* *h ?x *m (^ ?x (?n nump)) *t)                 (* *h (^ ?x ?new) *m *t)  ((?new (+ ?n 1))) )
  (exp-3      (* *h (^ ?x ?y) *m ?x *t)                        (* *h (^ ?x ?new) *m *t)  ((?new (se (list '+ ?y 1)))) )
  (exp-3bis   (* *h ?x *m (^ ?x ?y) *t)                        (* *h (^ ?x ?new) *m *t)  ((?new (se (list '+ ?y 1)))) )  
  (exp-6      (* *h (^ ?x ?y) *m (^ ?x ?z) *t)                 (* *h (^ ?x ?new) *m *t)  ((?new (se (list '+ ?y ?z)))) )
  (exp-4      (/ (^ ?x (?n nump)) *h ?x *t)                    (/ (^ ?x ?new) *h *t)     ((?new (- ?n 1))) )
  (exp-5      (/ (^ ?x ?y) *h ?x *t)                           (/ (^ ?x ?new) *h *t)     ((?new (se (list '- ?y 1)))) ) 
  (exp-7      (/ (^ ?x ?y) *h (^ ?x ?z) *t)                    (/ (^ ?x ?new) *h *t)     ((?new (se (list '- ?y ?z)))) )
  
  ; --- alla fine ordina alfabeticamente i termini
  (at-end     nil                                              sort-arith-ops            nil )
  
))

(defun in2pre(exp)(cond
  ((atom exp) exp)                 ; esempi: a, 1, nil
  ((atom (cdr exp)) exp)           ; esempi (a), (a.b)
  ((= (cadr exp) '+)(list '+ (in2pre (car exp))(in2pre (caddr exp))))
  ((= (cadr exp) '<)(list '< (in2pre (car exp))(in2pre (caddr exp))))
  (t exp)
))

  ;(se '(* (+ (^ x 2) (* b x))(+ c x)))
  ;(se '(* (- x y) (+ x y)))
