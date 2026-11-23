!(bind! &f (new-space))
!(add-atom &f (edge mother alice bob l1))
!(add-atom &f (edge mother alice bob l2))
!(add-atom &f (edge father bob carol r1))
!(bind! &seen (new-state 0))

(= (receive $x $m $z $i $j)
   (let $n (get-state &seen)
     (let $_ (change-state! &seen (+ 1 $n))
       (let $_ (if (== $n 0) (add-atom &f (edge father bob carol r2)) ())
         (yielded $n $x $m $z $i $j)))))

(= (snapshot $r $s $x $z)
   (transform &f (, (read (edge $r $x $m $i)) (read (edge $s $m $z $j)))
      (packet $x $m $z $i $j)))

; The right read opens when its particular left receipt reaches the continuation.
(= (live $r $s $x $z)
   (transform &f (read (edge $r $x $m $i))
     (transform &f (read (edge $s $m $z $j)) (packet $x $m $z $i $j))))

!(snapshot-results (collapse (let (packet $x $m $z $i $j) (snapshot mother father alice carol) (receive $x $m $z $i $j))))
!(after-snapshot (get-state &seen))
!(remove-atom &f (edge father bob carol r2))
!(change-state! &seen 0)
!(live-results (collapse (let (packet $x $m $z $i $j) (live mother father alice carol) (receive $x $m $z $i $j))))
!(after-live (get-state &seen))
