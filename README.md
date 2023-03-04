# yoctolisp
minimal lisp interpreter

The interpreter is a single small C file, there are just two more files if you want to debug memory usage.

### Build instruction
Run ./build.sh, the executable is "yoctolisp"

### Test
Cd to directory test, then all files with .l extension are small test case.


# Lisp language
Examples:

(defun ff(x) (if(atom x) x (ff(car x))))
(ff '((a b) c)) 
(+ 1 2 3 4)


