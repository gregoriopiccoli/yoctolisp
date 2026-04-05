(load "testsuite.l")
(load "compiler.l")

(defun let1(x)(let((x 100)) x))
(defun let2(x)(let((x 100)) x))
(compile 'let2)


; -- test suite --
(test-suite "-- Standard test suite --"

  (test (let1 1) 100  "test plain let")
  (test (let1 1) (let2 1) "test compiled let")

)
