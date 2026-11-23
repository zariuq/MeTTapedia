; Monotone closure over an immutable unary fact provider per round.
; Compiled code, signatures and the free carrier environment stay fixed.
; A pending search is retained intact. Only a complete publication batch is
; committed; receipt histories remain available with their original fact rows.

(: gslt:snapshot:rows (-> Atom Atom %Undefined%))
(= (gslt:snapshot:rows $relation $facts)
   (case $facts ((LNil LNil)
     ((LCons $fact $rest)
      (let $tail (gslt:snapshot:rows $relation $rest)
        (LCons (PremiseProviderRow $relation (LCons $fact LNil)) $tail))))))

(: gslt:snapshot:check-rows (-> Atom Atom Atom Atom Atom %Undefined%))
(= (gslt:snapshot:check-rows $declarations $free $bound $signatures $rows)
   (case $rows ((LNil True)
     ((LCons (PremiseProviderRow $relation $values) $rest)
      (let $arity (gslt:automata:length $values)
      (case (gslt:premise:signature $relation $arity
              (PremiseProvider $signatures $rows))
        ((None False)
         ((Some $signature)
          (if (gslt:premise:check-row $declarations $free $bound $signature
                 (PremiseProviderRow $relation $values))
            (gslt:snapshot:check-rows $declarations $free $bound $signatures $rest) False)))))))))

(: gslt:snapshot:plan (-> Atom Atom Atom Atom %Undefined%))
(= (gslt:snapshot:plan $plan $relation $facts $static)
   (case $plan
     (((CompletePlan (PremiseEnvironment $declarations $rewrites $specifications
           (PremiseProvider $signatures $oldRows) $reflection $free)
          $permissions $bound $expected $rules $equations $admitted)
       (let* (($factRows (gslt:snapshot:rows $relation $facts))
              ($rows (gslt:automata:append $factRows $static)))
         (if (gslt:snapshot:check-rows $declarations $free $bound $signatures $rows)
           (Some (CompletePlan (PremiseEnvironment $declarations $rewrites $specifications
                    (PremiseProvider $signatures $rows) $reflection $free)
                  $permissions $bound $expected $rules $equations $admitted)) None)))
      ($bad None))))

(: gslt:snapshot:binding (-> Atom Atom %Undefined%))
(= (gslt:snapshot:binding $name $assignment)
   (case $assignment ((LNil None)
     ((LCons (Binding $other (ContextualValue $dependencies $ambient $body)) $rest)
      (if (== $name $other)
        (if (== $dependencies LNil) (if (== $ambient 0) (Some $body) None) None)
        (gslt:snapshot:binding $name $rest))))))

(: gslt:snapshot:grounding (-> Atom Atom %Undefined%))
(= (gslt:snapshot:grounding $variables $assignment)
   (case $variables ((LNil (Some LNil))
     ((LCons (SnapshotVariable $sourceName $nativeName) $rest)
      (case (gslt:snapshot:binding $nativeName $assignment)
        ((None None)
         ((Some $value) (case (gslt:snapshot:grounding $rest $assignment)
           ((None None) ((Some $tail) (Some (LCons (Binding $sourceName $value) $tail))))))))))))

(: gslt:snapshot:premises (-> Atom Atom Atom %Undefined%))
(= (gslt:snapshot:premises $count $events $facts) (if (== $count 0) (Some LNil) (case $events ((LNil None) ((LCons (PremiseQueryEvent $index $quantifiers $row $origins) $rest) (if (== $quantifiers 0) (case (gslt:rule:row-at $row $facts) ((None None) ((Some $fact) (let $previous (- $count 1) (case (gslt:snapshot:premises $previous $rest $facts) ((None None) ((Some $tail) (Some (LCons $fact $tail))))))))) None)) ($bad None)))))

(: gslt:snapshot:firing (-> Atom Atom Atom %Undefined%))
(= (gslt:snapshot:firing $metadata $facts $receipt)
   (case $receipt
     (((ClassReceipt $representative $conversions
           (RuleJobReceipt (RuleJob $ordinal (RuleJobDeclaration $index $rule $bindingPlan) $site)
              $trace $captured $completed $history $local $target))
       (case (gslt:rule:row-at $index $metadata)
         ((None None)
          ((Some (SnapshotClause $statement $variables $positiveCount))
           (case (gslt:snapshot:grounding $variables $completed)
             ((None None)
              ((Some $grounding) (case (gslt:snapshot:premises $positiveCount $history $facts)
                ((None None) ((Some $premises)
                 (Some (SnapshotFiring (SnapshotKey $statement $grounding $premises) $target))))))))))))
      ($bad None))))

(: gslt:snapshot:commit (-> Atom Atom Atom Atom Atom Atom %Undefined%))
(= (gslt:snapshot:commit $metadata $snapshot $batch $facts $keys $newKeys)
   (case $batch
     ((LNil (Some (SnapshotCommit $facts $keys $newKeys)))
      ((LCons $receipt $rest)
       (case (gslt:snapshot:firing $metadata $snapshot $receipt)
         ((None None)
          ((Some (SnapshotFiring $key $fact))
           (let* (($factsNext (if (gslt:automata:member $fact $facts) $facts
                                  (gslt:automata:append $facts (LCons $fact LNil))))
                  ($seen (gslt:automata:member $key $keys))
                  ($keysNext (if $seen $keys (gslt:automata:append $keys (LCons $key LNil))))
                  ($added (if $seen $newKeys (gslt:automata:append $newKeys (LCons $key LNil)))))
             (gslt:snapshot:commit $metadata $snapshot $rest $factsNext $keysNext $added)))))))))

(: gslt:snapshot:begin (-> Atom Atom Atom Atom Atom Atom Atom %Undefined%))
(= (gslt:snapshot:begin $plan $standard $source $metadata $relation $static $seeds)
   (let $facts (gslt:automata:unique $seeds)
     (case (gslt:snapshot:plan $plan $relation $facts $static)
       ((None (SnapshotFailure InvalidProvider))
        ((Some $checked)
         (let $run (gslt:search:run ClassSearch $checked $source 0)
           (SnapshotClosure SnapshotPending 0 $checked $standard $source $metadata $relation $static
             $facts LNil LNil $run)))))))

(: gslt:snapshot:tick (-> Atom Atom %Undefined%))
(= (gslt:snapshot:tick $machine $quantum)
   (case $machine
     (((SnapshotClosure SnapshotPending $round $plan $standard $source $metadata $relation $static
           $facts $keys $history $run)
       (let $advanced (gslt:search:resume ClassSearch $plan $run $quantum)
         (if (== (gslt:search:status ClassSearch $plan $advanced) SearchComplete)
           (let $batch (gslt:search:publication ClassSearch $advanced)
             (case (gslt:snapshot:commit $metadata $facts $batch $facts $keys LNil)
               ((None (SnapshotFailure InvalidReceipt))
                ((Some (SnapshotCommit $nextFacts $nextKeys $newKeys))
                 (let* (($nextRound (+ $round 1))
                        ($nextHistory (gslt:automata:append $history
                          (LCons (SnapshotEpoch $round $facts $batch) LNil))))
                   (if (== $facts $nextFacts)
                     (SnapshotClosure SnapshotComplete $nextRound $plan $standard $source $metadata
                       $relation $static $nextFacts $nextKeys $nextHistory $advanced)
                     (case (gslt:snapshot:plan $plan $relation $nextFacts $static)
                       ((None (SnapshotFailure InvalidProvider))
                        ((Some $nextPlan)
                         (let $nextRun (gslt:search:run ClassSearch $nextPlan $source 0)
                           (SnapshotClosure SnapshotPending $nextRound $nextPlan $standard $source
                             $metadata $relation $static $nextFacts $nextKeys $nextHistory $nextRun)))))))))))
           (SnapshotClosure SnapshotPending $round $plan $standard $source $metadata $relation $static
             $facts $keys $history $advanced))))
      ($stopped $machine))))

(: gslt:snapshot:advance (-> Atom Atom Atom %Undefined%))
(= (gslt:snapshot:advance $machine $ticks $quantum)
   (if (== $ticks 0) $machine
     (let* (($next (gslt:snapshot:tick $machine $quantum)) ($remaining (- $ticks 1)))
       (gslt:snapshot:advance $next $remaining $quantum))))

(: gslt:snapshot:result (-> Atom %Undefined%))
(= (gslt:snapshot:result $machine)
   (case $machine
     (((SnapshotClosure $phase $round $plan $standard $source $metadata $relation $static
           $facts $keys $history $run) (SnapshotResult $phase $round $facts $keys))
      ($failure $failure))))
