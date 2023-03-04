(setq fibI (lambda(x) (if(< x 2) 1 (+(fibI(- x 1))(fibI(- x 2))))))
(setq fibS (#lambda (1 . 0) (if(< #A 2) 1 (+(fibS(- #A 1))(fibS(- #A 2))))))
(setq fibL (#lambda (1 . 0) (#lap "1!C#1!ClB1!ClBC" 2 < ("!" 1) 1 - fibL 2 - fibL +)))
(setq fib  (#lambdalap (1 . 0) ("1!C#1!Cb1!CbC" 2 < ("!" 1) 1 - fib 2 - fib +)))
(setq ff   (#lambdalap (1 . 0) ("1B#1Bb" atom ("1") car ff)))
(setq fac  (#lambdalap (1 . 0) ("1!C#11!CbC" 2 < ("!" 1) 1 - fac *)))


; --- fibonacci con una ricorsione dal basso ... prestazioni non confrontabili, come sempre l' algoritmo conta più di ogni tentativo di ottimizzazione!
(defun fibF(n)(if(< n 2) 1 (fibUp n 2 1 1)))
(defun fibUp(max count n1 n2)(if (= max count)(+ n1 n2)(fibUp max (+ count 1) (+ n1 n2) n1)))