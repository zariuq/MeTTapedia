; A pure polymorphic head can depend on mutable child annotation payloads.
!(let $left-type (new-state 1)
   (let $right-type (new-state 1)
     (let $added-a (add-atom &self (: a $left-type))
       (let $added-b (add-atom &self (: b $right-type))
         (let $added-f (add-atom &self (: f (-> $t $t R)))
           (let $target (new-state (f a b))
             (let $changed (change-state! $left-type 2)
               (change-state! $target (f a b)))))))))
