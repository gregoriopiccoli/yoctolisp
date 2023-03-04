; --- Unification Algorithm

; --- torna l' association list con i valori di ogni variabile
(defun Unify(pt1 pt2)(Unify-h1 pt1 pt2 nil))

; --- torna l' unificante tra due liste 
(defun Unificant(l1 l2)(let((unif (Unify-h1 l1 l2 nil)))(if (eq unif :failed) :failed (Unify-substUnif unif l1))))

; --- funzioni di servizio
(defun Unify-h1(pt1 pt2 lst)(cond
  ((eq lst :failed) :failed)
  ((Unify-varp pt1)(Unify-matchvar pt1 pt2 lst))
  ((Unify-varp pt2)(Unify-matchvar pt2 pt1 lst))
  ((Unify-constantp pt1)(cond
    ((equal pt1 pt2) lst)
    (t :failed)))
  ((Unify-constantp pt2) :failed)
  (t (Unify-h1 (cdr pt1) (cdr pt2)(Unify-h1 (car pt1) (car pt2) lst)))
))


(defun Unify-matchvar(var pt lst)(cond
  ((equal var pt) lst)
  (t (let ((bnd (assoc var lst)))(cond
       (bnd (Unify-h1 (cdr bnd) pt lst))
       ((Unify-occursp var pt) :failed)
       (t (cons (cons var pt) lst)))))
))

(defun Unify-occursp(var pt)(cond
  ((equal var pt) t)
  ((or (Unify-varp pt) (Unify-constantp pt)) nil)
  (t (or (Unify-occursp var (car pt))(Unify-occursp var (cdr pt))))
))

(defun Unify-constantp(item)(and (atom item) (<>(at "?" item)0)))

(defun Unify-varp(item)(=(at "?" item)0))

(defun Unify-substUnif(unif lst)(cond
  ((Unify-varp lst)(Unify-substUnifVar lst (assoc lst unif)))
  ((atom lst) lst)
  (t(cons(Unify-substUnif unif (car lst))(Unify-substUnif unif (cdr lst))))
))

(defun Unify-substUnifVar(var value)(if (null value) var (cdr value)))

