(= (alternatives) first)
(= (alternatives) (let $ignored (add-atom &self (mark)) (+ bad-value 3)))
!(let $f (quote alternatives) (collapse ($f)))
!(collapse (match &self (mark) present))
