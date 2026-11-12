; An immutable inferred range can depend on a mutable type in a head formal.
!(let $formal (new-state 1)
   (let $actual (new-state 1)
     (let $added-a (add-atom &self (: a $actual))
       (let $added-f (add-atom &self (: f (-> $formal R)))
         (let $target (new-state (f a))
           (let $changed (change-state! $formal 2)
             (change-state! $target (f a))))))))
