(load "testsuite.l")
(load "compiler.l")

(defun let1(x)(let((x 100)) x))
(defun let2(x)(let((x 100)) x))
(compile 'let2)


; -- test suite --
(test-suite "-- Compiled let test suite --"

  (test (let1 1) 100  "test plain let")
  (test (let1 1) (let2 1) "test compiled let")

  (test (count-let-vars '(let ((x 1)(y 2)) x)) 2 "test let 1")
  (test (count-let-vars '(let ((x 1)) (let((y 2)) x))) 2 "test let 2")
  (test (count-let-vars '(let ((x (let ((y 1)) y))) x)) 2 "test let 3")
  (test (count-let-vars '(let ((x 1)) (+ (let((y 1)) y) x))) 2 "test let 4")
  (test (count-let-vars '(+ (let((x 1)) x)(let((y 2)) y))) 2 "test let 5")
  
  (test (count-let-vars '(+ 1 2 3)) 0 "test let no-let 1")
  (test (count-let-vars '(lambda(x)x)) 0 "test let no-let 2")
)
