(defun NegNormForm(l)(cond
   ((atom l) l) 
   ((eq (car l) 'not)(NegNorm-Not (cadr l)))
   ((eq (car l) 'and)(cons 'and (NegNorm-PList (cdr l) 'and)))
   ((eq (car l) 'or) (cons 'or  (NegNorm-PList (cdr l) 'or)))
   ((eq (car l) '->)(list 'or (NegNorm-Not(cadr l))(NegNormForm(caddr l))))
   ((eq (car l) '<-)(list 'or (NegNormForm(cadr l))(NegNorm-Not(caddr l))))
   ((eq (car l) '<->)(NegNormForm (list 'and (list '-> (cadr l)(caddr l))(list '<- (cadr l)(caddr l)))))
   ((eq (car l) 'all)(list 'all (cadr l) (NegNormForm (caddr l))))
   ((eq (car l) 'exists)(list 'exists (cadr l) (NegNormForm (caddr l))))   
   (t l)
))

(defun NegNorm-Not(l)(cond
   ((atom l) (list 'not l))
   ((eq (car l) 'not)(NegNormForm(cadr l)))
   ((eq (car l) 'and)(cons 'or (NegNorm-PList (NegNorm-NList(cdr l)) 'or)))
   ((eq (car l) 'or) (cons 'and (NegNorm-PList (NegNorm-NList(cdr l)) 'and)))
   ((eq (car l) '->)(list 'and (NegNormForm(cadr l))(NegNorm-Not(caddr l))))                                                                       ; !!! manca il flatten della and
   ((eq (car l) '<-)(list 'and (NegNorm-Not(cadr l))(nnf(caddr l))))                                                                               ; !!! manca il flatten della and
   ((eq (car l) '<->)(list 'or (list 'and (NegNormForm(cadr l)) (NegNorm-Not(caddr l))) (list 'and (NegNorm-Not(cadr l)) (NegNormForm(caddr l))))) ; !!! mancano i flatten
   ((eq (car l) 'all)(list 'exists (cadr l) (NegNorm-Not(caddr l))))
   ((eq (car l) 'exists)(list 'all (cadr l) (NegNorm-Not(caddr l))))
   ((eq (car l) '=)  (list '<> (NegNormForm(cadr l))  (NegNormForm(caddr l))))  
   ((eq (car l) '<>) (list '=  (NegNormForm(cadr l))  (NegNormForm(caddr l))))  
   ((eq (car l) '>)  (list '<= (NegNormForm(cadr l))  (NegNormForm(caddr l))))  
   ((eq (car l) '>=) (list '<  (NegNormForm(cadr l))  (NegNormForm(caddr l))))  
   ((eq (car l) '<)  (list '>= (NegNormForm(cadr l))  (NegNormForm(caddr l))))  
   ((eq (car l) '<=) (list '>  (NegNormForm(cadr l))  (NegNormForm(caddr l))))  
   (t (list 'not l))
))

(defun NegNorm-PList(l op)(cond
  ((null l) nil)
  ((atom (car l))    (cons (car l) (NegNorm-PList (cdr l) op)))
  ((eq(caar l) op)   (append (NegNorm-PList (cdar l) op) (NegNorm-PList (cdr l) op)))
  (t                 (cons (NegNormForm (car l)) (NegNorm-PList (cdr l) op)))  
))

(defun NegNorm-NList(l)(cond
  ((null l) nil)
  (t (cons (NegNorm-Not(car l)) (NegNorm-NList (cdr l))))
))
