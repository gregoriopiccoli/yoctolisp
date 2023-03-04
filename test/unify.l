; --- Unification Algorithm

(defun unify(pt1 pt2 lst)(cond
   ((eq lst 'failed) 'failed)
   ((varp pt1)(matchvar pt1 pt2 lst))
   ((varp pt2)(matchvar pt2 pt1 lst))
   ((is-constant-p pt1)(cond
	   ((equal pt1 pt2) lst)
       (t 'failed)))
   ((is-constant-p pt2) 'failed)
   (t (unify (cdr pt1) (cdr pt2)(unify (car pt1) (car pt2) lst)))
))

(defun matchvar(var pt lst)(cond
   ((equal var pt) lst)
   (t (let ((bnd (assoc (cadr var) lst)))(cond
	  (bnd (unify (cdr bnd) pt lst))
	  ((occursp var pt) 'failed)
	  (t (cons (cons (cadr var) pt) lst)))))
))

(defun occursp (var pt)(cond
   ((equal var pt) t)
   ((or (varp pt) (is-constant-p pt)) nil)
   (t (or (occursp var (car pt))(occursp var (cdr pt))))
))

(defun is-constant-p(item)(atom item))

(defun varp (item)
  (and (not(atom item))
       (eq (car item) 'var)
	   (atom (cadr item))
	   (null (cddr item))))

(defun subst-unif(unif lst)(cond
    ((atom lst) lst)
    ((varp lst)(subst-unif-var lst (assoc (cadr lst) unif)))
    (t(cons(subst-unif unif (car lst))(subst-unif unif (cdr lst))))
))

(defun subst-unif-var(var value)(if (null value) var (cdr value)))

(defun unificant(l1 l2)(let((unif (unify l1 l2 nil)))(if (eq unif 'failed) 'failed (subst-unif unif l1))))

