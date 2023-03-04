(defun tst1()(mapcar 
  (lambda(x)(cons (car x)(reverse (remove (car x)(cdr x)))))
  '((a b c a b c)(b c d b c d)(c d e c d e)(d e f d e f))
))

(defun tst2()(map 
  (#lambdalap (1 . 0) ("1B1B1BCBC" car car cdr remove reverse cons)) 
  '((a b c a b c)(b c d b c d)(c d e c d e)(d e f d e f))
))

; --- prova con #lambda
(defun tst3()(map 
  (#lambda (1 . 0)(cons (car #A)(reverse (remove (car #A)(cdr #A)))))
  '((a b c a b c)(b c d b c d)(c d e c d e)(d e f d e f))
))

; --- scheme
;(define (tst1)(map 
;  (lambda(x)(cons (car x)(reverse (remove (car x)(cdr x)))))
;  '((a b c a b c)(b c d b c d)(c d e c d e)(d e f d e f))
;))

; --- picolisp
;(de tst1()(mapcar 
;  '((x)(cons (car x)(reverse (delete (car x)(cdr x)))))
;  '((a b c a b c)(b c d b c d)(c d e c d e)(d e f d e f))
;))

;; pico   0.8
;; femto       7.6 
;; yocto  9.0  8.1 --> con remove 6.7 --> con reverse 1.6 --> con #lambdalap 1.1
;; ecl    5.1  4.1
;; gcl    6.7  3.3
;; sbcl        1.6
;; clo         1.2
;; clisp 32.8 15.1
;; abcl   9.3  4.8
;; ikarus      1.2
;; xlisp  6.x
;; xlisp+ 3.7
