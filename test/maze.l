(setq maze '((1) (0 2) (1 6) (7 4) (3) (9) (2 7 10) (6 3 11) (U 12) (5 13) (6 14) (7 15) (8 16) (9 14) (10 13 15) (11 14 16) (12 15)))

(defun risolvi_labirinto(casella)(estendi_strada (nth casella maze) (cons casella nil) maze))

(defun estendi_strada(vicini strada labirinto)(cond
  ((null vicini) nil)                                                           ; non ci sono più caselle da provare, non si è trovata la strada
  ((eq (car vicini) 'U) strada)                                                 ; il primo vicino è l' uscita! trovata la strada per uscire
  ((member (car vicini) strada)(estendi_strada (cdr vicini) strada labirinto))  ; il primo vicino è già nella strada percorsa, lo salto
  (t 
    (let ((s (estendi_strada (nth (car vicini) labirinto) (cons (car vicini) strada) labirinto))) ; provo tutte le strade che partono dal primo vicino
      (cond
        ((null s)(estendi_strada (cdr vicini) strada labirinto))                ; se non ho trovato l' uscita passando dal primo vicino, provo con il prossimo vicino 
        (t s))))                                                                ; ho trovato l' uscita passando per un vicino 
))

;(
;(0 0 0 0 0 0 0 0 0)
;(0 1 1 0 1 1 1 1 1)
;(0 1 0 0 1 0 0 0 0)
;(0 1 0 1 1 1 1 1 0)
;(0 1 0 1 0 1 0 1 0)
;(0 1 1 1 0 1 0 1 0)
;(0 0 0 0 0 0 0 0 0) 
;)
