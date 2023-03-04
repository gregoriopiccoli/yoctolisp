
(defun Match(p s)
  ; --- funzione principale che crea l' assoc list vuota e chima la funzione di match
  (let((r (Match-h1 p s nil)))(if (or(= r :failed)(Match-CheckDuplicatedJolly r)) :failed r))
)

; --- funzione che esegue effetivamente il match tra liste costruendo l' assoc list tra le varibili e quanto trovato 
(defun Match-h1(p s a)(cond
  ((null p) (if (null s) a :failed))               ; p è finita, se anche s è finita le due liste matchano, altrimenti no
  ((or (atom p)(atom s))(cond 
    ((eq p s) a)                                   ; sono due atomi, se sono uguali matchano
    ((Match-Varp p)                                ; altrimenti bisogna verificare se p è una variabile
      (let((aa (assoc p a)))(cond                  ; cerca se c'è già la varibile
        ((null aa)(cons (cons p s) a))             ; se non c'è la aggiunge
        ((eq p (cdr aa)) a)                        ; se c'è deve essere uguale
        (t :failed)                                ; è una variabile ma c'è già con un altro valore
    ))) 
    ((Match-Seqp p) (cons(cons p s)a))                        ; p è un jolly, prende tutto quello che segue
    ((and (not(atom p))(Match-Seqp (car p))(null (cdr p)))    ; è il caso speciale del jolly a fine lista e la seconda lista è all' ultimo elemento (null o atomo)
      (cons (cons (car p) s) a))
    ((and (not(atom p))(Match-Seqp (car p))(equal (cdr p) s)) ; è il caso speciale del jolly a un passo dalla fine e la seconda lista è all' ultimo elemento (null o atomo)
      (cons (cons (car p) nil) a))
    (t :failed)                                    ; non sono atomi uguali e p non è una variabile
  ))
  ; --- da qui sia p che s sono liste
  ((equal (car p) (car s))                         ; confronta i due primi elementi di p ed s, se sono uguali matcha il resto delle due liste 
    (Match-h1 (cdr p)(cdr s) a))
    ((Match-Varp(car p))                           ; verifica il carattere jolly nella lista p
      (let((aa (assoc (car p) a)))(cond            ; controlla se la variabile è già stata associata ad un valore
        ((null aa)(Match-h1 (cdr p)(cdr s) (cons(cons (car p) (car s)) a)))   ; se nuova crea il nuovo valore per la variabile e continua il confronto
        ((equal (cdr aa) (car s))(Match-h1 (cdr p)(cdr s) a))                 ; se già definita deve coincidere il nuovo valore con il precedente per continuare il confronto
        (t :failed)                                                           ; la variabile esisteva ed il nuovo match ha valori diversi
    )))  
    ((and (Match-ConstrainedVar(car p))(Match-VerifyConstraint(car p)(car s))); verifica il carattere jolly nella lista p
      (let((aa (assoc (caar p) a)))(cond                                      ; controlla se la variabile è già stata associata ad un valore
        ((null aa)(Match-h1 (cdr p)(cdr s) (cons(cons (caar p) (car s)) a)))  ; se nuova crea il nuovo valore per la variabile e continua il confronto
        ((equal (cdr aa) (car s))(Match-h1 (cdr p)(cdr s) a))                 ; se già definita deve coincidere il nuovo valore con il precedente per continuare il confronto
        (t :failed)                                                           ; la variabile esisteva ed il nuovo match ha valori diversi
    )))  
    ((Match-Seqp(car p))(let((r1 (Match-h1 (cdr p) s a))) ; provo se matcha quello che segue con l' intera lista analizzata
      (if (<> r1 :failed)
        (cons (cons (car p) nil) r1)                      ; la lista che segue matcha, quindi questo jolly viene messo a vuoto
        (let((r2 (Match-h1 (cdr p)(cdr s) a)))            ; provo a fare il match delle due parti che seguono
          (if (<> r2 :failed)
            (cons (cons (car p)(cons (car s) nil)) r2)    ; il jolly matcha con la parte inziale della lista 
            (let((r3 (Match-h1 p (cdr s) a)))             ; provo a matchare il jolly con la parte che segue della lista
              (if (<> r3 :failed)
                (Match-Extend (car p)(car s) r3)          ; è andata bene, estendo il jolly con il pezzo che avevo tolto dall' inizio della lista
                :failed))))
    )))   
    (t (let((aa (Match-h1 (car p)(car s) a))) ; costruisce il match tra i primi due elementi
         (if (= aa :failed)                   ; se falliesce tra i primi due
           :failed                            ; fallisce tutto
           (Match-h1 (cdr p)(cdr s) aa))      ; matcha il resto delle liste con le varibili aggiunte dai primi due elementi
    )) 
))
  
; --- funzione che indica se il pattern trovato è una variabile 
(defun Match-Varp(x)(=(at "?" x)0))

; --- funzione che indica se il pattern trovato è una variabile jolly
(defun Match-Seqp(x)(=(at "*" x)0))

; --- funzione che estende quanto finora associato ad una variabile jolly
(defun Match-Extend(x v a)(let((r (assoc x a)))(progn (rplacd r (cons v (cdr r))) a)))
    
; --- funzione che indica se un pattern è una variabile con constraint
(defun Match-ConstrainedVar(x)(and(not(atom x))(Match-Varp(car x))(consp (cdr x))(null (cddr x))))

; --- funzione che verifica il constraint associato ad una variabile rispetto a quanto sta tentando di matchare
(defun Match-VerifyConstraint(x s)((cadr x) s))

; --- funzione di verifica che non ci siano variabili jolly con valori diversi tra loro
(defun Match-CheckDuplicatedJolly(a)
   (if (null a) 
     nil
     (let((r (car a)))
       (if (Match-Seqp (car r))
         (let ((aa(assoc (car r) (cdr a))))
           (if (or(null aa)(equal r aa))
             (Match-CheckDuplicatedJolly (cdr a)) 
             :failed))
         (Match-CheckDuplicatedJolly(cdr a))             
     ))
))
