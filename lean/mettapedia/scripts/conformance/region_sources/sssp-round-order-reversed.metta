(sd 0 0)
(e 0 2 9)
(e 0 1 2)
(e 1 2 3)
(e 2 3 1)

(= (improve $space $vertex $candidate)
  (let $current (collapse (match $space (sd $vertex $previous) $previous))
    (if (== $current ())
      (let $discard (add-atom $space (sd $vertex $candidate)) $vertex)
      (let ($previous) $current
        (if (< $candidate $previous)
          (let* (($discard (remove-atom $space (sd $vertex $previous)))
                 ($discard (add-atom $space (sd $vertex $candidate)))) $vertex)
          (empty))))))

(= (relax $u)
  (match (quote &self) (sd $u $d)
    (match (quote &self) (e $u $vertex $w)
      (improve &self $vertex (+ $d $w)))))

(= (sssp $front $round)
  (let $next (collapse (unique (let $u (superpose $front) (relax $u))))
    (if (== $next ()) $round (sssp $next (+ $round 1)))))

!(sssp (0) 0)
!(collapse (match &self (sd $vertex $distance) (quote ($vertex $distance))))
