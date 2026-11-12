; A private argument aliases the returned polymorphic argument.
(: Known A)
(: Known B)
(: alias-bind (-> $t $u $t))
(= (alias-bind $a $b) (let $b Known $a))
!(collapse (alias-bind $x $x))
