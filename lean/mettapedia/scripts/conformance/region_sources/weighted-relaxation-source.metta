(sd 0 0)
(sd 1 10)
(e 0 1 3)
(e 0 1 3)
(e 0 2 4)
(e 0 0 0)

(= (improve $space $vertex $candidate)
  (let $current (collapse (match $space (sd $vertex $previous) $previous))
    (if (== $current ())
      (let $discard (add-atom $space (sd $vertex $candidate)) $vertex)
      (let ($previous) $current
        (if (< $candidate $previous)
          (let* (($discard (remove-atom $space (sd $vertex $previous)))
                 ($discard (add-atom $space (sd $vertex $candidate)))) $vertex)
          (empty))))))

!(collapse (let $space &self (let $u 0
  (match (quote &self) (sd $u $d)
    (match (quote &self) (e $u $vertex $w)
      (improve $space $vertex (+ $d $w)))))))
!(collapse (match &self (sd $vertex $distance) (quote ($vertex $distance))))
!(collapse (let $space &self (let $u 0
  (match (quote &self) (sd $u $d)
    (match (quote &self) (e $u $vertex $w)
      (improve $space $vertex (+ $d $w)))))))
!(collapse (match &self (e $u $vertex $w) (quote ($u $vertex $w))))
!(+ 18446744073709551616 1)
