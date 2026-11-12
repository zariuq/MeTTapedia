; Candidate for a head binding introduced by a later operand.
(: vanish (-> Number Number))
(= (vanish $ignored) (empty))
(: expose (-> $t %Undefined% $t))
(= (expose $anchor $slot) (let $slot vanish $anchor))
(: outer (-> $t $t))
(= (outer $a) (let $ignored ($h (expose 0 $h)) $a))
!(collapse (outer 1))
