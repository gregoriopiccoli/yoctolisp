(load "testsuite.l")
(load "compiler.l")

(defun let1(x)(let((x 100)) x))
(defun let2(x)(let((x 100)) x))
(compile 'let2)

(defun let3(x)(let((y 10)(z 100)(k 1000))(+ x y z k)))
(defun let4(x)(let((y 10)(z 100)(k 1000))(+ x y z k)))
(compile 'let4)

(defun let5(x)(let((y 10))(let((z 100))(+ x y z))))
(defun let6(x)(let((y 10))(let((z 100))(+ x y z))))
(compile 'let6)

(defun let7(x)(let((y (let((k 10))k)))(let((z 100))(+ x y z))))
(defun let8(x)(let((y (let((k 10))k)))(let((z 100))(+ x y z))))
(compile 'let8)

(defun let9(x) (let((y 10)(k 100))(let((z 1000))(+ x y z k))))
(defun let10(x)(let((y 10)(k 100))(let((z 1000))(+ x y z k))))
(compile 'let10)

; -- test suite --
(test-suite "-- Compiled let test suite --"

  (test (let1 1) 100  "test plain let")
  (test (let1 1) (let2 1) "test compiled let 1-2")
  (test (let3 1) (let4 1) "test compiled let 3-4")
  (test (let5 1) (let6 1) "test compiled let 5-6")
  (test (let7 1) (let8 1) "test compiled let 7-8")
  (test (let9 1) (let10 1) "test compiled let 9-10")

  (test (count-let-vars '(let ((x 1)(y 2)) x)) 2 "test let 1")
  (test (count-let-vars '(let ((x 1)) (let((y 2)) x))) 2 "test let 2")
  (test (count-let-vars '(let ((x (let ((y 1)) y))) x)) 2 "test let 3")
  (test (count-let-vars '(let ((x 1)) (+ (let((y 1)) y) x))) 2 "test let 4")
  (test (count-let-vars '(+ (let((x 1)) x)(let((y 2)) y))) 2 "test let 5")
  
  (test (count-let-vars '(+ 1 2 3)) 0 "test let no-let 1")
  (test (count-let-vars '(lambda(x)x)) 0 "test let no-let 2")
)
