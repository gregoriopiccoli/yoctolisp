; --- negation normal form

(defun nnf(f)(cond
  ((atom f)f)
  ((eq (car f) 'not)(nnf-not (cadr f)))
  ((eq (car f) 'and)(cons 'and (map nnf (cdr f))))
  ((eq (car f) 'or)(cons 'or (map nnf (cdr f))))
  ((eq (car f) '->)(list 'or (nnf-not(cadr f))(nnf(caddr f))))
  ((eq (car f) '<-)(list 'or (nnf(cadr f))(nnf-not(caddr f))))
  ((eq (car f) '<->)(nnf (list 'and (list '-> (cadr f)(caddr f))(list '<- (cadr f)(caddr f)))))
  ((eq (car f) 'all)(list 'all (cadr f) (nnf (caddr f))))
  ((eq (car f) 'exists)(list 'exists (cadr f) (nnf (caddr f))))
  (t f)
))

(defun nnf-not(f)(cond
  ((atom f) (list 'not f))
  ((eq (car f) 'not)(nnf (cadr f)))
  ((eq (car f) 'and)(cons 'or (map (lambda(x)(nnf(list 'not x))) (cdr f))))
  ((eq (car f) 'or)(cons 'and (map (lambda(x)(nnf(list 'not x))) (cdr f))))
  ((eq (car f) '->)(list 'and (nnf(cadr f))(nnf-not(caddr f))))
  ((eq (car f) '<-)(list 'and (nnf-not(cadr f))(nnf(caddr f))))
  ((eq (car f) '<->)(list 'or (list 'and (nnf(cadr f)) (nnf-not(caddr f))) (list 'and (nnf-not(cadr f)) (nnf(caddr f)))))
  ((eq (car f) 'all)(list 'exists (cadr f) (nnf-not(caddr f))))
  ((eq (car f) 'exists)(list 'all (cadr f) (nnf-not(caddr f))))
  (t (list 'not f))
))

; appiattisce sull' operazione primaria {es: (and (and a b) c) -> (and a b c)}

(defun flatten(l)(flatOps '(and or) l))

(defun flatOps(ops l)(cond
  ((atom l) l)
  ((member(car l) ops)(cons (car l)(flatOp (car l) (cdr l) ops)))
  (t l)
))

(defun flatOp(op l ops)(cond 
  ((null l) nil)                                              ; la lista è finita ...
  ((atom (car l))                                             ; se il primo elemento è un atomo 
    (cons (car l)(flatOp op (cdr l) ops)))                    ;   appiattisce il resto della lista per l' operazione corrente
  ((eq (caar l) op)                                           ; se il primo elemento è una lista ed il suo primo elemento è l' operazione che sto appiattendo
    (append (flatOp op (cdar l) ops)(flatOp op (cdr l) ops))) ;   appiattisce il primo elemento sull' operazione corrente e lo unisce all' appiattimento del resto della lista
  (t                                                          ; altrimenti
    (cons (flatOps ops (car l))(flatOp op (cdr l) ops)))      ;   appiattisce sulle altre operazioni la testa della lista e la unisce all' appiattimento sull' operazione corrente del resto della lista 
))

; --- tableaux ---
;
; scomporre, fermarsi al primo modello
;
(defun tblx(cf of lit nlit) (cond
  ((null cf) nil)
  ((atom cf)(cond
     ((member cf nlit) nil)                            ; se un literal è nella lista dei negati il ramo si chiude
     ((null of)(cons (add-lit cf lit) nlit))           ; se non ci sono altre formule ritorna le due liste di literals
     (t (tblx (car of)(cdr of) (add-lit cf lit) nlit)) ; prosegue mettendo la formula nella lista dei positivi
  ))
  ; --- not --------------
  ((eq (car cf) 'not)(cond
    ((atom (cadr cf))(cond
      ((member (cadr cf) lit) nil)                             ; se un literal negato è nella lista dei literal il ramo si chiude
      ((null of)(cons lit (add-lit (cadr cf) nlit)))           ; se non ci sono altre formule ritornna le due liste di literals
      (t (tblx (car of)(cdr of) lit (add-lit (cadr cf) nlit))) ; prosegue mettendo la formula nella lista dei negativi
    ))
    (t (cond
      ; --- not not
      ((eq (caadr cf) 'not)(tblx (cadadr cf) of lit nlit))
      ; --- not and
      ((eq (caadr cf) 'and)(tblx (cons 'or (map put-not (cdadr cf))) of lit nlit))
      ; --- not or
      ((eq (caadr cf) 'or)(tblx (cons 'and (map put-not (cdadr cf))) of lit nlit))
      ; --- not ->
      ((eq (caadr cf) '->)(tblx (list 'and (cadadr cf) (list 'not (caddadr cf))) of lit nlit))
      ; --- not <-
      ((eq (caadr cf) '<-)(tblx (list 'and (list 'not (cadadr cf)) (caddadr cf)) of lit nlit))
      ; --- not <->
      ((eq (caadr cf) '<->) (tblx (list 'or (list 'and (cadadr cf) (list 'not (caddadr cf))) (list 'and (list 'not (cadadr cf))(caddadr cf))) of lit nlit))
      (t (princ "*****  not impl *****" cf))
    ))
  ))
  ; --- and --------------
  ((eq (car cf) 'and) (tblx (cadr cf) (append (cddr cf) of) lit nlit)) ;
  ; --- or --------------
  ((eq (car cf) 'or)
    (let((tmp (tblx (cadr cf) of lit nlit)))     ; valuta la prima subformula nella or
      (if (and(null tmp)(not(null(cddr cf))))    ; se non ha trovato un modello e ci sono ancora formule prosegue
        (tblx (cons 'or (cddr cf)) of lit nlit)  ; valuta il resto della or
        tmp                                      ; altrimenti torna il modello trovato
      )
    )
    ;---- questa versione torna tutti i modelli che trova
    ;(if (null (cdr cf)) nil
    ;  (cons
    ;    (tblx (cadr cf) of lit nlit)
    ;    (tblx (cons 'or (cddr cf)) of lit nlit))
    ;)
  )
  ; --- -> --------------
  ;((eq (car cf) '->) (tblx (list 'or (list 'not (cadr cf))(caddr cf)) of lit nlit)) ; si può fare meglio ...
  ;((eq (car cf) '<-) (tblx (list 'or (list 'not (caddr cf))(cadr cf)) of lit nlit))
  ((eq (car cf) '->) (let((tmp (tblx (list 'not (cadr cf)) of lit nlit)))(if tmp tmp (tblx (caddr cf) of lit nlit)))) ; questa versione segue alla lettera i tableaux
  ((eq (car cf) '<-) (let((tmp (tblx (cadr cf) of lit nlit)))(if tmp tmp (tblx (list 'not (caddr cf)) of lit nlit))))
  ((eq (car cf) '<->) (tblx (list 'and (list 'or (list 'not (cadr cf)) (caddr cf)) (list 'or (cadr cf) (list 'not (caddr cf)))) of lit nlit))
  ;
  (t (princ "*****  not impl *****" cf))
))
(defun put-not(x)(list 'not x))

(defun theo(theorem . hypothesis)(theo-2 (tblx (list 'not theorem) hypothesis nil nil)))
(defun theo-2(x)(if (null x) t x))

; aggiunge un literal alla lista se non c'e' già
(defun add-lit(x lit)(if(member x lit) lit (cons x lit)))

;-------- versione precedente che torna tutti i modelli trovati
;(defun theo(theorem . hypothesis)(theo-1 (tblx (list 'not theorem) hypothesis nil nil)))
;(defun theo-1(x)(theo-2 (filter (lambda(x)(not(null x))) x)))

(theo '(->(and(not a)(-> b a))(or(not a)b)))
