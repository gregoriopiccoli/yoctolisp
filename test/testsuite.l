(defun test(v1 v2 msg)(let((r (equal v1 v2)))(if r r (progn (princ msg " fail " v1 "<>" v2  " " :nl) r))))

(defun test-suite-2(t-ok t-fail lst)
  (cond
    ((null lst)(princln "ok=" t-ok " fail=" t-fail))
    ((car lst) (test-suite-2 (+ 1 t-ok) t-fail (cdr lst)))
    (t (test-suite-2  t-ok (+ 1 t-fail) (cdr lst)))
))

(defun test-suite (title . lst) (progn (princln title) (test-suite-2 0 0 lst)))
