; prime prove per un Assembler per il linguaggio LAP

(defun asm(f) (cond
  ((atom f)(asm-atom f (celltype f)))    ; asm di un atomo
  ((atom (car f)) (asm-funcall f))       ; asm della chiamata di una funzione
  (t :not-asm)
))

(defun asm-atom(a ty)(cond
  ((null a) (list :load-nil))
  ((= a t)  (list :load-t))
  ((= ty 1) (list (if (hashsymp a) :load-local-var :load-var) a))
  ((= ty 2) (list :load-keyword a))
  ((= ty 3) (list :load-num-const a))
  ((= ty 4) (list :load-str-const a))
  (t :not-asm)
))

(defun asm-funcall(e)(cond
  ((= (car e) 'quote) (list :quote e)) ; qui c'è il punto da sviluppare ... come riesco a fare QUOTE??? fatto questo vengono le macro
  ((= (car e) 'if)    (asm-if e))
  ((= (car e) 'cond)  (list :cond e))
  (t (asm-funcprms (cdr e) (car e)))
))

(defun asm-funcprms(prms fun)(cond
  ((null prms) (list :call-fun fun))          ; finiti i parametri chiama la funzione
  (t (asm-funcprm (car prms)(cdr prms) fun))  ; 
))

(defun asm-funcprm(p prms fun) (cons (asm p) (asm-funcprms prms fun)))

(defun asm-if(e)(list (asm (cadr e)) :jump-if (asm (caddr e)) (asm (cadddr e))))

