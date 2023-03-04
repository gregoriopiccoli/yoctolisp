; ---  Yocto pairlis e assoc ---
;
; Il lisp 1.5 descrive in poche righe il funzionamento dell' interprete, che così 
; risulta avere una semantica chiarissima.
; Due funzioni però caratterizzano in modo molto forte tutta la costruzione, e 
; sono la pairlis e la assoc. Di fatto queste funzioni costrituiscono la symbol
; table che mantiene i valori delle variabili e gestisce la loro visibilità.
; Il lisp 1.5 realizza il "dynamic scoping", ma con pochissime variazioni si 
; riesce ad implementare anche il "lexical scoping".
;
; Il problema della coppia "pairlis" e "assoc" è che sono molto poco performanti.
; 
; nuove funzioni per sostituire la "pairlis" e la "assoc" del lisp  1.5 in yoctolisp
; con queste  
; 
; --- ATTENZIONE: cambia profondamente anche la set! ---
;

; costruisce la "association list" di yoctolisp, sostituisce la "pairlis" del lisp 1.5
; ypair(n:(list sym) v:(list any) l:yplist):yplist
(defun ypair(n v al)(cons (cons n v) al))

; cerca un nome in una yplist, sostituisce la "assoc" del lisp 1.5
; yassoc(n:sym al:yplist):any
(defun yassoc(n al)
  (if (null al)  
    nil 
    (let((r (yfind n (caar al) (cdar al)))) 
      (if (null r) 
        (yassoc n (cdr al)) 
        (cons n r)                          ; torna la coppia (<nome> . <valore>) per indicare che è stato trovato un valore, nil non può essere usato!
      )
    )
  )
)

; cerca un nome in una singola lista di nomi e se lo trova ritorna il valore nella posizione corrispondente nella lista di valori
; yfind(n:sym nl:(list sym) vl:(list any)):any
(defun yfind(n nl vl)
  (cond
    ((null nl) nil)                   ; non ha trovato il nome 
    ((atom nl) (if (eq n nl) vl nil)) ; il caso di lista derivata da una parametro "vararg"
    ((eq n (car nl)) (car vl))        ; trovato al primo posto, ritorna il valore
    (t (yfind n (cdr nl) (cdr vl)))   ; il nome non è al primo posto, scorre le due liste
  )
)

; assegna un valore ad una variabile contenuta nella associacion list; torna il valore se trovata, nil altrimenti
;
(defun yset(n v al)
  (if (null al) 
    nil                            ; non ha trovato il nome, non esegue nessuna assegnazione
    (if (atom (caar al))           ; all' inizio della lista trova una coppia (a . ?)
      (if (eq (caar al) n)         ; se è il nome che cerca
        (cdr(rplacd (car al)v))    ; sostituisce il vecchio valore con il nuovo
        (yset n v (cdr al))        ; altrimenti prosegue nell' esplorazione della lista           
      )
      (let((r (yset-l n v (caar al)(cdar al)))) ; prova a cercare nella lista
        (if (null r)                            ; se non lo trova
          (yset n v (cdr al))                   ; prosegue sulla lista
          v                                     ; torna il valore 
        )
      )
    )      
  )
)

(defun yset-l (n v nl vl)
  (cond
     ((null nl) nil)
     ((atom nl) (error "ERROR: Trying to set a 'vararg' "))
     ((eq n (car nl))(cons n (car(rplaca vl v))))  
     (t (yset-l n v (cdr nl)(cdr vl)))
  )
)

(yassoc 'a '(((alfa beta).("a" "b"))(a . 1)(b . (2 2 2))((x y . z).(10 20 30 40)))) ; --> 1
(yassoc 'b '(((alfa beta).("a" "b"))(a . 1)(b . (2 2 2))((x y . z).(10 20 30 40)))) ; --> (2 2 2)
(yassoc 'x '(((alfa beta).("a" "b"))(a . 1)(b . (2 2 2))((x y . z).(10 20 30 40)))) ; --> 10
(yassoc 'z '(((alfa beta).("a" "b"))(a . 1)(b . (2 2 2))((x y . z).(10 20 30 40)))) ; --> (30 40)
(yassoc 'alfa '(((alfa beta).("a" "b"))(a . 1)(b . (2 2 2))((x y . z).(10 20 30 40)))) ; --> "a"
(yassoc 'beta '(((alfa beta).("a" "b"))(a . 1)(b . (2 2 2))((x y . z).(10 20 30 40)))) ; --> "b"
   
(defun part(f l)(if (null l) nil (cons (cons   (if (f (car l)) :left :right )  (car l) ) (part f (cdr l)) )))
(defun separate(l side)(if (null l) nil (if (eq (caar l) side) (cons (cdar l) (separate (cdr l) side)) (separate (cdr l) side))))