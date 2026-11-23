; Package port over the refined ground CHR controller.
; A run pairs the controller machine with the identifiers given to its
; posted seeds, newest first. Seeds are posted from the bottom goal task;
; that task is the only task exactly when its next seed is introduced, and
; the introduction gives that seed the machine's next identifier.
; The adapter reads controller states; it never constructs one.

(: gslt:chr-lang:begin (-> Atom %Undefined%))
(= (gslt:chr-lang:begin $machine) (ChrLangRun $machine LNil))

(: gslt:chr-lang:advance (-> Atom Number %Undefined%))
(= (gslt:chr-lang:advance $run $quantum)
   (case $run
     (((ChrLangRun $machine $seeds)
        (case $machine
          (((ChrMachine ChrPending $plan $standard $predicates $scalars $entries
               (LCons (ChrGoals LNil (LCons (ChrTell $head) $goals)) LNil)
               $store $next $history $receipts)
             (ChrLangRun (gslt:chr:tick $machine $quantum) (LCons $next $seeds)))
           ($other (ChrLangRun (gslt:chr:tick $machine $quantum) $seeds))))))))

; One bounded unit of work: up to $ticks controller ticks, each recorded by
; gslt:chr-lang:advance, stopping at a terminal machine.
(: gslt:chr-lang:run-ticks (-> Atom Number Number %Undefined%))
(= (gslt:chr-lang:run-ticks $run $ticks $quantum)
   (if (== $ticks 0) $run
     (case $run
       (((ChrLangRun (ChrMachine ChrPending $plan $standard $predicates $scalars $entries $tasks $store $next $history $receipts) $seeds)
          (let $advanced (gslt:chr-lang:advance $run $quantum)
            (gslt:chr-lang:run-ticks $advanced (- $ticks 1) $quantum)))
        ($terminal $run)))))

(: gslt:chr-lang:reverse (-> Atom Atom %Undefined%))
(= (gslt:chr-lang:reverse $items $done)
   (case $items
     ((LNil $done)
      ((LCons $first $rest) (gslt:chr-lang:reverse $rest (LCons $first $done))))))

; A terminal machine yields its phase, final store and seed identifiers in
; posting order. A pending machine is not an outcome.
(: gslt:chr-lang:outcome (-> Atom %Undefined%))
(= (gslt:chr-lang:outcome $run)
   (case $run
     (((ChrLangRun $machine $seeds)
        (case $machine
          (((ChrMachine $phase $plan $standard $predicates $scalars $entries $tasks $store $next $history $receipts)
             (if (== $phase ChrPending) LangPortPendingV1
               (LangPortDoneV1 (ChrLangResult $phase $store (gslt:chr-lang:reverse $seeds LNil)))))))))))
