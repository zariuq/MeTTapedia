(: hold (-> Atom Atom))
(= (hold $x) $x)
!(hold (println! 9))
!(let $f (quote hold) ($f (println! 9)))
