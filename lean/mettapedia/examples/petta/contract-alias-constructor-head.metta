; One declaration keeps the space functional. Binding a formerly open head
; can change an expression's type from a tuple type to a constructor range.
(: Known (-> Number Tag))
(: alias-bind-u (-> $t %Undefined% $t))
(= (alias-bind-u $a $b) (let $b Known $a))
(= (entry-head $ignored) (alias-bind-u ($x 1) $x))
(= (entry-data $ignored) (alias-bind-u (Data $x) $x))
(: launch (-> Number Number))
(= (launch $ignored) (let $result (alias-bind-u ($x 1) $x) 1))
!(collapse (alias-bind-u ($x 1) $x))
!(collapse (entry-head 0))
!(collapse (alias-bind-u (Data $x) $x))
!(collapse (entry-data 0))
!(collapse (launch 0))
