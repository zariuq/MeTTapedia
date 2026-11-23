; A total query tick advances one retained candidate machine. Pending work
; stores the remaining candidates, answers and complete current search.
(: gslt:maude-query:begin (-> Atom Atom Atom Atom Atom %Undefined%))
(= (gslt:maude-query:begin $plan $standard $request $states $finished)
   (case $states
     ((LNil (MaudeQueryDone $finished))
      ((LCons $source $rest)
       (let $input (PApp $request (LCons $source LNil))
         (let $machine (gslt:runner:begin ClassSearch $plan $standard $input)
           (MaudeQueryActive $rest $finished $machine)))))))

(: gslt:maude-query:step (-> Atom Atom Atom Atom Atom Atom Number %Undefined%))
(= (gslt:maude-query:step $plan $standard $request $solution $wrapper $controller $quantum)
   (case $controller
     (((MaudeQueryDone $answers) $controller)
      ((MaudeQueryFault $error $rest $answers $machine) $controller)
      ((MaudeQueryActive $rest $answers $machine)
       (let $next (gslt:runner:tick ClassSearch $plan $standard $machine $quantum)
         (case $next
           (((ClassMachine ClassDone
                (PApp $label (LCons (PCollection "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.hashBag" $residual RNone) LNil))
                $search $history $receipts)
             (if (== $label $solution)
               (let $answer (PApp $wrapper
                     (LCons (PCollection "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.hashBag" $residual RNone) LNil))
                 (gslt:maude-query:begin $plan $standard $request $rest (LCons $answer $answers)))
               (MaudeQueryFault "UnexpectedResult" $rest $answers $next)))
            ((ClassMachine ClassDone (PApp $label (LCons (PApp $state-wrapper $body) LNil)) $search $history $receipts)
             (if (== $label $request)
               (gslt:maude-query:begin $plan $standard $request $rest $answers)
               (MaudeQueryFault "UnexpectedResult" $rest $answers $next)))
            ((ClassMachine ClassDone $bad $search $history $receipts)
             (MaudeQueryFault "UnexpectedResult" $rest $answers $next))
            ($pending (MaudeQueryActive $rest $answers $pending)))))))))

(: gslt:maude-query:advance (-> Atom Atom Atom Atom Atom Number Number Atom %Undefined%))
(= (gslt:maude-query:advance $plan $standard $request $solution $wrapper $ticks $quantum $controller)
   (if (> $ticks 0)
     (let* (($next (gslt:maude-query:step $plan $standard $request $solution $wrapper $controller $quantum))
            ($remaining (- $ticks 1)))
       (gslt:maude-query:advance $plan $standard $request $solution $wrapper $remaining $quantum $next))
     $controller))

(: gslt:maude-query:export (-> Atom Atom Atom Atom Atom Atom %Undefined%))
(= (gslt:maude-query:export $plan $standard $request $solution $wrapper $controller)
   (case $controller
     (((MaudeQueryDone $answers) $answers)
      ((MaudeQueryFault $error $rest $answers $machine) $controller)
      ((MaudeQueryActive $rest $answers $machine)
       (MaudeQueryPending $plan $standard $request $solution $wrapper $controller)))))

(: gslt:maude-query:filter (-> Atom Atom Atom Atom Atom Atom Atom Number Number %Undefined%))
(= (gslt:maude-query:filter $plan $standard $request $solution $wrapper $states $finished $ticks $quantum)
   (let* (($begun (gslt:maude-query:begin $plan $standard $request $states $finished))
          ($next (gslt:maude-query:advance $plan $standard $request $solution $wrapper $ticks $quantum $begun)))
     (gslt:maude-query:export $plan $standard $request $solution $wrapper $next)))

(: gslt:maude-query:resume (-> Atom Number Number %Undefined%))
(= (gslt:maude-query:resume (MaudeQueryPending $plan $standard $request $solution $wrapper $controller) $ticks $quantum)
   (let $next (gslt:maude-query:advance $plan $standard $request $solution $wrapper $ticks $quantum $controller)
     (gslt:maude-query:export $plan $standard $request $solution $wrapper $next)))
(= (gslt:maude-query:resume LNil $ticks $quantum) LNil)
(= (gslt:maude-query:resume (LCons $first $rest) $ticks $quantum) (LCons $first $rest))
(= (gslt:maude-query:resume (MaudeQueryFault $error $rest $answers $machine) $ticks $quantum)
   (MaudeQueryFault $error $rest $answers $machine))
