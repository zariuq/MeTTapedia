(= (choose-let-star) 1)
(= (choose-let-star) 2)
!(let* (($x (choose-let-star)) ($y (+ $x 10))) (pair $x $y))
