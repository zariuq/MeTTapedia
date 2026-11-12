(sat 10 1)
(= (in $f $x) invented)
(= (in $f $x)
  (not (== (collapse (once (match &self (sat $f $x) t))) ())))

!(collapse (if (in 10 1) (quote held) (quote not-held)))

(: raw-in (-> Atom Atom Bool))
(= (raw-in $f $x)
  (not (== (collapse (once (match &self (sat $f $x) t))) ())))
!(collapse (if (raw-in 10 1) (quote held) (quote not-held)))
