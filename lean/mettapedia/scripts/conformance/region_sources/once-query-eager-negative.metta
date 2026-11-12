(sat 1 7)
(sat 1 7)
!(index-atom
   (collapse (superpose ((match &self (sat 1 7) true)
                         (let $_ (println! tail-effect) outside))))
   0)
