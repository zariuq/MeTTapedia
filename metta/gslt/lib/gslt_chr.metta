(: gslt:chr:nibble (-> Number %Undefined%))
(: gslt:chr:nibble-value (-> Atom %Undefined%))
(= (gslt:chr:nibble 0) (PApp "R16Nibble0" LNil))
(= (gslt:chr:nibble-value (PApp "R16Nibble0" LNil)) 0)
(= (gslt:chr:nibble 1) (PApp "R16Nibble1" LNil))
(= (gslt:chr:nibble-value (PApp "R16Nibble1" LNil)) 1)
(= (gslt:chr:nibble 2) (PApp "R16Nibble2" LNil))
(= (gslt:chr:nibble-value (PApp "R16Nibble2" LNil)) 2)
(= (gslt:chr:nibble 3) (PApp "R16Nibble3" LNil))
(= (gslt:chr:nibble-value (PApp "R16Nibble3" LNil)) 3)
(= (gslt:chr:nibble 4) (PApp "R16Nibble4" LNil))
(= (gslt:chr:nibble-value (PApp "R16Nibble4" LNil)) 4)
(= (gslt:chr:nibble 5) (PApp "R16Nibble5" LNil))
(= (gslt:chr:nibble-value (PApp "R16Nibble5" LNil)) 5)
(= (gslt:chr:nibble 6) (PApp "R16Nibble6" LNil))
(= (gslt:chr:nibble-value (PApp "R16Nibble6" LNil)) 6)
(= (gslt:chr:nibble 7) (PApp "R16Nibble7" LNil))
(= (gslt:chr:nibble-value (PApp "R16Nibble7" LNil)) 7)
(= (gslt:chr:nibble 8) (PApp "R16Nibble8" LNil))
(= (gslt:chr:nibble-value (PApp "R16Nibble8" LNil)) 8)
(= (gslt:chr:nibble 9) (PApp "R16Nibble9" LNil))
(= (gslt:chr:nibble-value (PApp "R16Nibble9" LNil)) 9)
(= (gslt:chr:nibble 10) (PApp "R16Nibble10" LNil))
(= (gslt:chr:nibble-value (PApp "R16Nibble10" LNil)) 10)
(= (gslt:chr:nibble 11) (PApp "R16Nibble11" LNil))
(= (gslt:chr:nibble-value (PApp "R16Nibble11" LNil)) 11)
(= (gslt:chr:nibble 12) (PApp "R16Nibble12" LNil))
(= (gslt:chr:nibble-value (PApp "R16Nibble12" LNil)) 12)
(= (gslt:chr:nibble 13) (PApp "R16Nibble13" LNil))
(= (gslt:chr:nibble-value (PApp "R16Nibble13" LNil)) 13)
(= (gslt:chr:nibble 14) (PApp "R16Nibble14" LNil))
(= (gslt:chr:nibble-value (PApp "R16Nibble14" LNil)) 14)
(= (gslt:chr:nibble 15) (PApp "R16Nibble15" LNil))
(= (gslt:chr:nibble-value (PApp "R16Nibble15" LNil)) 15)

; Experimental controller; source-to-native qualification remains open.
; Refined ground CHR control over the existing resumable GSLT search.
; A search publication proposes a head match. Guards and propagation history
; authorize its commit. Body goals run before a surviving active constraint
; resumes at the same rule/head occurrence.

(: gslt:chr:lookup (-> Atom Atom %Undefined%))
(= (gslt:chr:lookup $name $environment)
   (case $environment ((LNil None)
     ((LCons (Binding $other $value) $rest)
       (if (== $name $other) (Some $value) (gslt:chr:lookup $name $rest))))))

(: gslt:chr:zip-environment (-> Atom Atom %Undefined%))
(= (gslt:chr:zip-environment $variables $values)
   (case $variables
     ((LNil (if (== $values LNil) (Some LNil) None))
      ((LCons $name $rest)
       (case $values ((LNil None)
         ((LCons $value $tail)
          (case (gslt:chr:zip-environment $rest $tail)
            ((None None) ((Some $environment) (Some (LCons (Binding $name $value) $environment))))))))))))

(: gslt:chr:digits-value (-> Atom %Undefined%))
(= (gslt:chr:digits-value $digits)
   (case $digits ((LNil 0)
     ((LCons $digit $tail)
       (+ (gslt:chr:nibble-value $digit) (* 16 (gslt:chr:digits-value $tail)))))))

(: gslt:chr:digits (-> Number %Undefined%))
(= (gslt:chr:digits $number)
   (if (== $number 0) LNil
     (case (gslt:integer:divmod $number 16)
       (((IntegerDivmod $quotient $remainder)
         (let $digit (gslt:chr:nibble $remainder)
           (if (== $quotient 0) (LCons $digit LNil)
             (LCons $digit (gslt:chr:digits $quotient)))))))))

(: gslt:chr:encode-integer (-> Number %Undefined%))
(= (gslt:chr:encode-integer $number)
   (let* (($negative (< $number 0))
          ($magnitude (if $negative (- 0 $number) $number))
          ($sign (PApp (if $negative "ChrNegative" "ChrNonnegative") LNil)))
     (PApp "ChrIntegerDigits" (LCons $sign
       (LCons (PCollection "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.vec" (gslt:chr:digits $magnitude) RNone) LNil)))))

(: gslt:chr:decode-integer (-> Atom %Undefined%))
(= (gslt:chr:decode-integer $value)
   (case $value
     (((PApp "ChrIntegerDigits" (LCons (PApp $sign LNil)
           (LCons (PCollection "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.vec" $digits RNone) LNil)))
       (let $magnitude (gslt:chr:digits-value $digits)
         (if (== $sign "ChrNegative") (Some (- 0 $magnitude))
           (if (== $sign "ChrNonnegative") (Some $magnitude) None))))
      ($other None))))

(: gslt:chr:next-id (-> Atom %Undefined%))
(= (gslt:chr:next-id $id)
   (case $id
     (((PApp "ChrOccurrenceNumber" (LCons (PCollection "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.vec" $digits RNone) LNil))
       (PApp "ChrOccurrenceNumber" (LCons
         (PCollection "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.vec" (gslt:chr:digits (+ (gslt:chr:digits-value $digits) 1)) RNone) LNil))))))

(: gslt:chr:term (-> Atom Atom %Undefined%))
(= (gslt:chr:term $environment $term)
   (case $term
     (((ChrLiteral $value) (Some $value))
      ((ChrVariable $name) (gslt:chr:lookup $name $environment))
      ((ChrTuple $fields)
       (case (gslt:chr:terms $environment $fields)
         ((None None) ((Some $values) (Some (PApp "ChrTuple" (LCons (PCollection "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.vec" $values RNone) LNil))))))))))

(: gslt:chr:terms (-> Atom Atom %Undefined%))
(= (gslt:chr:terms $environment $terms)
   (case $terms ((LNil (Some LNil))
     ((LCons $term $tail)
       (case (gslt:chr:term $environment $term)
         ((None None) ((Some $value)
           (case (gslt:chr:terms $environment $tail)
             ((None None) ((Some $values) (Some (LCons $value $values))))))))))))

(: gslt:chr:constraint (-> Atom Atom %Undefined%))
(= (gslt:chr:constraint $environment $head)
   (case $head
     (((ChrHead $predicate $arguments)
       (case (gslt:chr:terms $environment $arguments)
         ((None None) ((Some $values)
           (Some (PApp "ChrConstraint" (LCons $predicate (LCons (PCollection "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.vec" $values RNone) LNil)))))))))))

(: gslt:chr:expression (-> Atom Atom %Undefined%))
(= (gslt:chr:expression $environment $expression)
   (case $expression
     (((ChrNumber $negative $magnitude) (Some (if $negative (- 0 $magnitude) $magnitude)))
      ((ChrIntVariable $name)
       (case (gslt:chr:lookup $name $environment)
         ((None (ChrArithmeticFault (Unbound $name)))
          ((Some $value)
           (case (gslt:chr:decode-integer $value)
             ((None (ChrArithmeticFault (NonInteger $value))) ((Some $number) (Some $number))))))))
      ((ChrIntOperation $operator $left $right)
       (case (gslt:chr:expression $environment $left)
         (((ChrArithmeticFault $fault) (ChrArithmeticFault $fault))
          ((Some $leftValue)
           (case (gslt:chr:expression $environment $right)
             (((ChrArithmeticFault $fault) (ChrArithmeticFault $fault))
              ((Some $rightValue) (gslt:chr:operation $operator $leftValue $rightValue)))))))))))

(: gslt:chr:operation (-> Atom Number Number %Undefined%))
(= (gslt:chr:operation $operator $left $right)
   (case $operator
     ((ChrAdd (Some (+ $left $right)))
      (ChrSubtract (Some (- $left $right)))
      (ChrMultiply (Some (* $left $right)))
      ($division
       (if (== $right 0) (ChrArithmeticFault DivisionByZero)
         (let* (($a (if (< $left 0) (- 0 $left) $left))
                ($b (if (< $right 0) (- 0 $right) $right)))
           (case (gslt:integer:divmod $a $b)
             (((IntegerDivmod $magnitude $residual)
               (let* (($quotient (if (== (< $left 0) (< $right 0)) $magnitude (- 0 $magnitude)))
                      ($remainder (- $left (* $quotient $right))))
                 (case $division
                   ((ChrQuotient (Some $quotient))
                    (ChrRemainder (Some $remainder))
                    (ChrModulo (Some (if (== $remainder 0) 0
                      (if (== (< $remainder 0) (< $right 0)) $remainder (+ $remainder $right)))))))))))))))))

(: gslt:chr:comparison (-> Atom Number Number %Undefined%))
(= (gslt:chr:comparison $operator $left $right)
   (case $operator
     ((ChrEqual (== $left $right)) (ChrDifferent (if (== $left $right) False True))
      (ChrLess (< $left $right)) (ChrLessEqual (if (> $left $right) False True))
      (ChrGreater (> $left $right)) (ChrGreaterEqual (if (< $left $right) False True)))))

(: gslt:chr:guard (-> Atom Atom %Undefined%))
(= (gslt:chr:guard $environment $guard)
   (case $guard
     (((ChrIdentity $left $right)
       (case (gslt:chr:term $environment $left)
         ((None (ChrArithmeticFault (Uninstantiated $left)))
          ((Some $first) (case (gslt:chr:term $environment $right)
            ((None (ChrArithmeticFault (Uninstantiated $right)))
             ((Some $second) (Some (== $first $second)))))))))
      ((ChrDifference $left $right)
       (case (gslt:chr:guard $environment (ChrIdentity $left $right))
         (((Some $answer) (Some (if $answer False True)))
          ((ChrArithmeticFault $fault) (ChrArithmeticFault $fault)))))
      ((ChrCompare $operator $left $right)
       (case (gslt:chr:expression $environment $left)
         (((ChrArithmeticFault $fault) (ChrArithmeticFault $fault))
          ((Some $first) (case (gslt:chr:expression $environment $right)
            (((ChrArithmeticFault $fault) (ChrArithmeticFault $fault))
             ((Some $second) (Some (gslt:chr:comparison $operator $first $second))))))))))))

(: gslt:chr:guards (-> Atom Atom %Undefined%))
(= (gslt:chr:guards $environment $guards)
   (case $guards ((LNil (Some True))
     ((LCons $guard $tail)
       (case (gslt:chr:guard $environment $guard)
         (((ChrArithmeticFault $fault) (ChrArithmeticFault $fault))
          ((Some $answer) (if $answer (gslt:chr:guards $environment $tail) (Some False)))))))))

(: gslt:chr:ids (-> Atom %Undefined%))
(= (gslt:chr:ids $occurrences)
   (case $occurrences ((LNil LNil)
     ((LCons (PApp "ChrOccurrence" (LCons $id (LCons $constraint LNil))) $tail)
       (LCons $id (gslt:chr:ids $tail))))))

; Head order belongs to CHR. Canonical GSLT publication order is not a
; partner-selection policy: suspended partners are tried newest first.
(: gslt:chr:match-target (-> Atom Atom %Undefined%))
(= (gslt:chr:match-target $standard $receipt)
   (let $target (gslt:search:target ClassSearch $standard $receipt)
     (case $target
       (((PApp "ChrMatched" (LCons (PCollection "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.vec" $values RNone)
            (LCons (PApp "ChrHeads" (LCons (PCollection "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.vec" $kept RNone) LNil))
             (LCons (PApp "ChrHeads" (LCons (PCollection "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.vec" $removed RNone) LNil))
              (LCons (PApp "ChrStore" (LCons (PCollection "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.hashBag" $rest RNone) LNil)) LNil)))))
         (ChrMatch $values $kept $removed $rest))
        ($bad (ChrChoiceFault InvalidReceipt))))))

(: gslt:chr:newer-ids (-> Atom Atom %Undefined%))
(= (gslt:chr:newer-ids $left $right)
   (case ($left $right)
     (((LNil LNil) False)
      ((LNil $rest) True)
      (($rest LNil) False)
      (((LCons $first $tail) (LCons $second $rest))
        (if (== $first $second) (gslt:chr:newer-ids $tail $rest)
          (case ($first $second)
            ((((PApp "ChrOccurrenceNumber" (LCons (PCollection "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.vec" $a RNone) LNil))
               (PApp "ChrOccurrenceNumber" (LCons (PCollection "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.vec" $b RNone) LNil)))
              (> (gslt:chr:digits-value $a) (gslt:chr:digits-value $b))))))))))

(: gslt:chr:prefer-receipt (-> Atom Atom Atom %Undefined%))
(= (gslt:chr:prefer-receipt $standard $left $right)
   (let* (($one (gslt:chr:match-target $standard $left))
          ($two (gslt:chr:match-target $standard $right)))
     (case ($one $two)
       ((((ChrMatch $valuesA $keptA $removedA $restA) (ChrMatch $valuesB $keptB $removedB $restB))
         (let* (($selectedA (gslt:automata:append $keptA $removedA))
                ($selectedB (gslt:automata:append $keptB $removedB))
                ($first (gslt:chr:ids $selectedA)) ($second (gslt:chr:ids $selectedB)))
           (if (== $first $second) True (gslt:chr:newer-ids $first $second))))
        ($bad False)))))

(: gslt:chr:insert-receipt (-> Atom Atom Atom %Undefined%))
(= (gslt:chr:insert-receipt $standard $receipt $receipts)
   (case $receipts
     ((LNil (LCons $receipt LNil))
      ((LCons $first $rest)
        (if (gslt:chr:prefer-receipt $standard $receipt $first)
          (LCons $receipt $receipts)
          (LCons $first (gslt:chr:insert-receipt $standard $receipt $rest)))))))

(: gslt:chr:order-receipts (-> Atom Atom %Undefined%))
(= (gslt:chr:order-receipts $standard $receipts)
   (case $receipts
     ((LNil LNil)
      ((LCons $first $rest)
        (let $ordered (gslt:chr:order-receipts $standard $rest)
          (gslt:chr:insert-receipt $standard $first $ordered))))))

(: gslt:chr:choose (-> Atom Atom Atom Atom %Undefined%))
(= (gslt:chr:choose $standard $entry $history $batch)
   (case $entry
     (((ChrEntry $rule $query $variables $guards $body $propagation)
       (case $batch
         ((LNil ChrNoChoice)
          ((LCons $receipt $tail)
           (case (gslt:chr:match-target $standard $receipt)
             (((ChrMatch $values $kept $removed $rest)
               (let* (($selected (gslt:automata:append $kept $removed))
                      ($selectedIds (gslt:chr:ids $selected))
                      ($key (ChrKey $rule $selectedIds)))
                 (if (if $propagation (gslt:automata:member $key $history) False)
                   (gslt:chr:choose $standard $entry $history $tail)
                   (case (gslt:chr:zip-environment $variables $values)
                     ((None (ChrChoiceFault InvalidEnvironment))
                      ((Some $environment)
                       (case (gslt:chr:guards $environment $guards)
                         (((ChrArithmeticFault $fault) (ChrChoiceFault $fault))
                          ((Some $answer)
                           (if $answer (ChrChoice $environment $kept $removed $rest $key $receipt)
                             (gslt:chr:choose $standard $entry $history $tail)))))))))))
              ($fault $fault))))))))))

(: gslt:chr:begin (-> Atom Atom Atom Atom Atom Atom %Undefined%))
(= (gslt:chr:begin $plan $standard $predicates $scalars $entries $goals)
   (ChrMachine ChrPending $plan $standard $predicates $scalars $entries
     (LCons (ChrGoals LNil $goals) LNil) LNil
     (PApp "ChrOccurrenceNumber" (LCons (PCollection "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.vec" LNil RNone) LNil)) LNil LNil))

(: gslt:chr:with-phase (-> Atom Atom %Undefined%))
(=
  (gslt:chr:with-phase $machine $newPhase)
  (case
    $machine
    (((ChrMachine $phase $plan $standard $predicates $scalars $entries $tasks $store $next $history $receipts)
       (ChrMachine
         $newPhase
         $plan
         $standard
         $predicates
         $scalars
         $entries
         $tasks
         $store
         $next
         $history
         $receipts))
)))

(: gslt:chr:post-goal (-> Atom Atom Atom Atom Atom %Undefined%))
(=
  (gslt:chr:post-goal $machine $environment $goal $goals $tail)
  (case
    $machine
    (((ChrMachine $phase $plan $standard $predicates $scalars $entries $tasks $store $next $history $receipts)
       (case
         $goal
         (((ChrTell $head)
            (case
              (gslt:chr:constraint $environment $head)
              ((None (gslt:chr:with-phase $machine (ChrFault UninstantiatedConstraint)))
                ((Some $constraint)
                  (let*
                    (($occurrence (PApp "ChrOccurrence" (LCons $next (LCons $constraint LNil))))
                      ($newStore (gslt:automata:append $store (LCons $occurrence LNil))))
                    (ChrMachine
                      $phase
                      $plan
                      $standard
                      $predicates
                      $scalars
                      $entries
                      (LCons (ChrActive $next $entries) (LCons (ChrGoals $environment $goals) $tail))
                      $newStore
                      (gslt:chr:next-id $next)
                      $history
                      $receipts))))))
           ((ChrAssign $name $expression)
             (case
               (gslt:chr:expression $environment $expression)
               (((ChrArithmeticFault $fault) (gslt:chr:with-phase $machine (ChrFault $fault)))
                 ((Some $number)
                   (let*
                     (($value (gslt:chr:encode-integer $number)))
                     (case
                       (gslt:chr:lookup $name $environment)
                       ((None
                          (ChrMachine
                            $phase
                            $plan
                            $standard
                            $predicates
                            $scalars
                            $entries
                            (LCons (ChrGoals (LCons (Binding $name $value) $environment) $goals) $tail)
                            $store
                            $next
                            $history
                            $receipts))
                         ((Some $old)
                           (if
                             (== $old $value)
                             (ChrMachine
                               $phase
                               $plan
                               $standard
                               $predicates
                               $scalars
                               $entries
                               (LCons (ChrGoals (LCons (Binding $name $value) $environment) $goals) $tail)
                               $store
                               $next
                               $history
                               $receipts)
                             (ChrMachine
                               ChrFailed
                               $plan
                               $standard
                               $predicates
                               $scalars
                               $entries
                               $tasks
                               $store
                               $next
                               $history
                               $receipts))))))))))
           (ChrFail
             (ChrMachine
               ChrFailed
               $plan
               $standard
               $predicates
               $scalars
               $entries
               $tasks
               $store
               $next
               $history
               $receipts)))))
)))

(: gslt:chr:start-active (-> Atom Atom Atom Atom %Undefined%))
(=
  (gslt:chr:start-active $machine $active $remaining $tail)
  (case
    $machine
    (((ChrMachine $phase $plan $standard $predicates $scalars $entries $tasks $store $next $history $receipts)
       (let*
         (($ids (gslt:chr:ids $store)))
         (if
           (gslt:automata:member $active $ids)
           (case
             $remaining
             ((LNil
                (ChrMachine
                  $phase
                  $plan
                  $standard
                  $predicates
                  $scalars
                  $entries
                  $tail
                  $store
                  $next
                  $history
                  $receipts))
               ((LCons (ChrEntry $rule $query $variables $guards $body $propagation) $rest)
                 (let*
                   (($source
                      (PApp
                        $query
                        (LCons
                          $predicates
                          (LCons
                            $scalars
                            (LCons
                              $active
                              (LCons (PApp "ChrStore" (LCons (PCollection "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.hashBag" $store RNone) LNil)) LNil))))))
                     ($run (gslt:search:run ClassSearch $plan $source 0)))
                   (ChrMachine
                     $phase
                     $plan
                     $standard
                     $predicates
                     $scalars
                     $entries
                     (LCons (ChrSearching $active $remaining $run) $tail)
                     $store
                     $next
                     $history
                     $receipts)))))
           (ChrMachine
             $phase
             $plan
             $standard
             $predicates
             $scalars
             $entries
             $tail
             $store
             $next
             $history
             $receipts))))
)))

(: gslt:chr:commit-choice (-> Atom Atom Atom Atom Atom Atom %Undefined%))
(=
  (gslt:chr:commit-choice $machine $active $entry $restEntries $tail $choice)
  (case
    $machine
    (((ChrMachine $phase $plan $standard $predicates $scalars $entries $tasks $store $next $history $receipts)
       (case
         $choice
         (((ChrChoice $environment $kept $removed $rest $key $receipt)
            (case
              $entry
              (((ChrEntry $rule $query $variables $guards $body $propagation)
                 (let*
                   (($newStore (gslt:automata:append $kept $rest))
                     ($newHistory (if $propagation (LCons $key $history) $history))
                     ($removedIds (gslt:chr:ids $removed))
                     ($continuation
                       (if
                         (gslt:automata:member $active $removedIds)
                         $tail
                         (LCons (ChrActive $active (LCons $entry $restEntries)) $tail)))
                     ($newReceipts (gslt:automata:append $receipts (LCons (ChrFiring $key $receipt) LNil))))
                   (ChrMachine
                     $phase
                     $plan
                     $standard
                     $predicates
                     $scalars
                     $entries
                     (LCons (ChrGoals $environment $body) $continuation)
                     $newStore
                     $next
                     $newHistory
                     $newReceipts)))
)))
)))
)))

(: gslt:chr:resume-search (-> Atom Atom Atom Atom Atom Number %Undefined%))
(= (gslt:chr:resume-search $machine $active $remaining $run $tail $quantum)
   (case $machine
     (((ChrMachine $phase $plan $standard $predicates $scalars $entries $tasks $store $next $history $receipts)
       (case $remaining
         (((LCons $entry $restEntries)
           (let $advanced (gslt:search:resume ClassSearch $plan $run $quantum)
             (if (== (gslt:search:status ClassSearch $plan $advanced) SearchComplete)
               (let* (($publication (gslt:search:publication ClassSearch $advanced))
                      ($ordered (gslt:chr:order-receipts $standard $publication))
                      ($choice (gslt:chr:choose $standard $entry $history $ordered)))
                 (case $choice
                   ((ChrNoChoice
                     (ChrMachine $phase $plan $standard $predicates $scalars $entries
                       (LCons (ChrActive $active $restEntries) $tail) $store $next $history $receipts))
                    ((ChrChoiceFault $fault) (gslt:chr:with-phase $machine (ChrFault $fault)))
                    ($chosen (gslt:chr:commit-choice $machine $active $entry $restEntries $tail $chosen)))))
               (ChrMachine $phase $plan $standard $predicates $scalars $entries
                 (LCons (ChrSearching $active $remaining $advanced) $tail)
                 $store $next $history $receipts)))))))))
)

(: gslt:chr:tick (-> Atom Number %Undefined%))
(=
  (gslt:chr:tick $machine $quantum)
  (case
    $machine
    (((ChrMachine
        ChrPending
        $plan
        $standard
        $predicates
        $scalars
        $entries
        $tasks
        $store
        $next
        $history
        $receipts)
       (case
         $tasks
         ((LNil
            (ChrMachine
              ChrComplete
              $plan
              $standard
              $predicates
              $scalars
              $entries
              $tasks
              $store
              $next
              $history
              $receipts))
           ((LCons (ChrGoals $environment LNil) $tail)
             (ChrMachine
               ChrPending
               $plan
               $standard
               $predicates
               $scalars
               $entries
               $tail
               $store
               $next
               $history
               $receipts))
           ((LCons (ChrGoals $environment (LCons $goal $goals)) $tail)
             (gslt:chr:post-goal $machine $environment $goal $goals $tail))
           ((LCons (ChrActive $active $remaining) $tail)
             (gslt:chr:start-active $machine $active $remaining $tail))
           ((LCons (ChrSearching $active $remaining $run) $tail)
             (gslt:chr:resume-search $machine $active $remaining $run $tail $quantum)))))
      ($terminal $terminal))))

(: gslt:chr:advance (-> Number Number Atom %Undefined%))
(= (gslt:chr:advance $ticks $quantum $machine)
   (if (== $ticks 0) $machine
     (case $machine
       (((ChrMachine ChrPending $plan $standard $predicates $scalars $entries $tasks $store $next $history $receipts)
         (let $advanced (gslt:chr:tick $machine $quantum)
           (gslt:chr:advance (- $ticks 1) $quantum $advanced)))
        ($terminal $terminal)))))

(: gslt:chr:constraints (-> Atom %Undefined%))
(= (gslt:chr:constraints $store)
   (case $store ((LNil LNil)
     ((LCons (PApp "ChrOccurrence" (LCons $id (LCons $constraint LNil))) $tail)
       (LCons $constraint (gslt:chr:constraints $tail))))))

(: gslt:chr:result (-> Atom %Undefined%))
(= (gslt:chr:result $machine)
   (case $machine
     (((ChrMachine $phase $plan $standard $predicates $scalars $entries $tasks $store $next $history $receipts)
       (ChrResult $phase (PCollection "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.hashBag" (gslt:chr:constraints $store) RNone) $history $receipts)))))
