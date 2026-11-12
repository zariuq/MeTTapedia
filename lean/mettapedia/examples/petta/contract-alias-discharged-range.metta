; The open head and the ANY argument alias. A trusted caller discharges
; the callee's result check, exposing the changed constructor type.
(: Known (-> Number Tag))
(: alias-bind-u (-> $t %Undefined% $t))
(= (alias-bind-u $a $b) (let $b Known $a))
(: launch (-> Number Number))
(= (launch $ignored) (let $result (alias-bind-u ($x 1) $x) 1))
!(collapse (launch 0))
