; The complete GSLT step search (OSLF/MeTTaIL/Complete in Lean).
; Load after gslt_scoped_execution, gslt_typed_sites and gslt_descent_execution.
;
; Arguments of these heads are data (Atom): bind computed values with let before passing them.

; ---------------------------------------------------------------------------
; Deepening over a family of scheduled goals (Complete.Deep).
;
; Families:
;   (RootFamily bound type source index admitted)  - a rule at a focus; certified by the
;     bound (nodes source) when admitted is Admitted (else Unadmitted).
;   (PremisesFamily context premises captured limit) - an equation's premises; certified by
;     the limit (Some depth) when its premises descend (EquationJob.premisesBound), else None.
; State: (DeepState depth level published), level a PremiseState.
; A drained level is certified when no branch was cut, or the depth reaches the bound.

(: gslt:deep:nodes (-> Atom %Undefined%))
(= (gslt:deep:nodes $pattern)
   (case $pattern
     (((Var $index) 1)
      ((FVar $name) 1)
      ((PApp $label $arguments) (let $inner (gslt:deep:nodes-list $arguments) (+ 1 $inner)))
      ((PLam $binder $body) (let $inner (gslt:deep:nodes $body) (+ 1 $inner)))
      ((PMultiLam $arity $binders $body) (let $inner (gslt:deep:nodes $body) (+ 1 $inner)))
      ((PSubst $body $replacement)
       (let* (($left (gslt:deep:nodes $body)) ($right (gslt:deep:nodes $replacement))) (+ 1 (+ $left $right))))
      ((PCollection $kind $elements $rest) (let $inner (gslt:deep:nodes-list $elements) (+ 1 $inner))))))

(: gslt:deep:nodes-list (-> Atom %Undefined%))
(= (gslt:deep:nodes-list $patterns)
   (case $patterns
     ((LNil 0)
      ((LCons $pattern $rest)
       (let* (($head (gslt:deep:nodes $pattern)) ($tail (gslt:deep:nodes-list $rest))) (+ $head $tail))))))

(: gslt:deep:goal (-> Atom Atom %Undefined%))
(= (gslt:deep:goal $family $depth)
   (case $family
     (((RootFamily $bound $type $source $index $admitted) (DescentRootGoal $depth $bound $type $source $index))
      ((PremisesFamily $context $premises $captured $limit) (DescentPremisesGoal $depth $context $premises $captured)))))

(: gslt:deep:bounded (-> Atom Atom %Undefined%))
(= (gslt:deep:bounded $family $depth)
   (case $family
     (((RootFamily $bound $type $source $index $admitted)
       (if (== $admitted Admitted) (let $size (gslt:deep:nodes $source) (<= $size $depth)) False))
      ((PremisesFamily $context $premises $captured $limit)
       (case $limit ((None False) ((Some $size) (<= $size $depth))))))))

(: gslt:deep:level-start (-> Atom Atom Atom %Undefined%))
(= (gslt:deep:level-start $family $depth $published)
   (let* (($goal (gslt:deep:goal $family $depth))
          ($level (gslt:descent:start $goal)))
     (DeepState $depth $level $published)))

(: gslt:deep:start (-> Atom %Undefined%))
(= (gslt:deep:start $family) (gslt:deep:level-start $family 0 LNil))

(: gslt:deep:fresh (-> Atom Atom %Undefined%))
(= (gslt:deep:fresh $published $answers)
   (case $answers
     ((LNil LNil)
      ((LCons $answer $rest)
       (let $tail (gslt:deep:fresh $published $rest)
         (if (gslt:automata:member $answer $published) $tail (LCons $answer $tail)))))))

(: gslt:deep:publication (-> Atom %Undefined%))
(= (gslt:deep:publication $state)
   (case $state
     (((DeepState $depth (PremiseState $agenda $answers $unresolved $work) $published)
       (let* (($payloads (gslt:descent:payloads $answers))
              ($fresh (gslt:deep:fresh $published $payloads)))
         (gslt:automata:append $published $fresh))))))

(: gslt:deep:certified (-> Atom Atom %Undefined%))
(= (gslt:deep:certified $family $state)
   (case $state
     (((DeepState $depth (PremiseState $agenda $answers $unresolved $work) $published)
       (if (gslt:descent:cut $unresolved) (gslt:deep:bounded $family $depth) True)))))

(: gslt:deep:drained (-> Atom %Undefined%))
(= (gslt:deep:drained $state)
   (case $state
     (((DeepState $depth (PremiseState LNil $answers $unresolved $work) $published) True)
      ($pending False))))

(: gslt:deep:complete (-> Atom Atom %Undefined%))
(= (gslt:deep:complete $family $state)
   (if (gslt:deep:drained $state) (gslt:deep:certified $family $state) False))

(: gslt:deep:tick (-> Atom Atom Atom %Undefined%))
(= (gslt:deep:tick $environment $family $state)
   (case $state
     (((DeepState $depth $level $published)
       (if (gslt:deep:drained $state)
         (if (gslt:deep:certified $family $state)
           $state
           (let* (($next (+ $depth 1))
                  ($whole (gslt:deep:publication $state)))
             (gslt:deep:level-start $family $next $whole)))
         (let $advanced (gslt:descent:tick $environment $level)
           (DeepState $depth $advanced $published)))))))

; ---------------------------------------------------------------------------
; List helpers.

(: gslt:complete:drop (-> Atom Atom %Undefined%))
(= (gslt:complete:drop $count $items)
   (if (== $count 0) $items
     (case $items
       ((LNil LNil)
        ((LCons $item $rest) (let $previous (- $count 1) (gslt:complete:drop $previous $rest)))))))


; ---------------------------------------------------------------------------
; Every rule job of a term, in fair rounds (Complete.Step).
;
; Plan: (CompletePlan environment permissions bound expected rules equations admitted).
; State: (StepState entries log), entries (StepEntry job deep).

(: gslt:step:family (-> Atom Atom %Undefined%))
(= (gslt:step:family $admitted $job)
   (case $job
     (((RuleJob $ordinal $declaration (RuleJobSite $address $context $focus $focusBound $focusType $frames))
       (RootFamily $focusBound $focusType $focus $ordinal $admitted)))))

(: gslt:step:entries (-> Atom Atom %Undefined%))
(= (gslt:step:entries $admitted $jobs)
   (case $jobs
     ((LNil LNil)
      ((LCons $job $rest)
       (let* (($family (gslt:step:family $admitted $job))
              ($deep (gslt:deep:start $family))
              ($tail (gslt:step:entries $admitted $rest)))
         (LCons (StepEntry $job $deep) $tail))))))

(: gslt:step:begin (-> Atom Atom %Undefined%))
(= (gslt:step:begin $plan $source)
   (case $plan
     (((CompletePlan (PremiseEnvironment $declarations $rewrites $specifications $provider $reflection $free)
         $permissions $bound $expected $rules $equations $admitted)
       (let* (($jobs (gslt:sites:jobs $declarations $free $permissions $bound $expected $source $rules))
              ($entries (gslt:step:entries $admitted $jobs)))
         (StepState $entries LNil))))))

; The receipts of new firings of a job, checked at its site.
(: gslt:step:lift (-> Atom Atom Atom Atom Atom %Undefined%))
(= (gslt:step:lift $plan $source $job $answers $permissions)
   (case $answers
     ((LNil LNil)
      ((LCons $answer $rest)
       (case $plan
         (((CompletePlan $environment $planPermissions $bound $expected $rules $equations $admitted)
           (case $job
             (((RuleJob $ordinal $declaration (RuleJobSite $address $context $focus $focusBound $focusType $frames))
               (let* (($request (RuleJobRequestProjection $environment $planPermissions $bound $expected $source $job))
                      ($result (PremiseResult (RootGoal $focusBound $focusType $focus $ordinal) $answer))
                      ($finished (gslt:rule:job-finish-root $request $result))
                      ($tail (gslt:step:lift $plan $source $job $rest $permissions)))
                 (case $finished
                   (((Some $receipt) (LCons $receipt $tail))
                    (None $tail))))))))))))))

(: gslt:step:advance (-> Atom Atom Atom %Undefined%))
(= (gslt:step:advance $plan $source $entry)
   (case $plan
     (((CompletePlan $environment $permissions $bound $expected $rules $equations $admitted)
       (case $entry
         (((StepEntry $job $deep)
           (let* (($family (gslt:step:family $admitted $job))
                  ($before (gslt:deep:publication $deep))
                  ($count (gslt:automata:length $before))
                  ($next (gslt:deep:tick $environment $family $deep))
                  ($after (gslt:deep:publication $next))
                  ($new (gslt:complete:drop $count $after))
                  ($receipts (gslt:step:lift $plan $source $job $new $permissions)))
             (StepAdvanced (StepEntry $job $next) $receipts)))))))))

(: gslt:step:advance-all (-> Atom Atom Atom %Undefined%))
(= (gslt:step:advance-all $plan $source $entries)
   (case $entries
     ((LNil (StepAdvanced LNil LNil))
      ((LCons $entry $rest)
       (let* (($head (gslt:step:advance $plan $source $entry))
              ($tail (gslt:step:advance-all $plan $source $rest)))
         (case $head
           (((StepAdvanced $nextEntry $receipts)
             (case $tail
               (((StepAdvanced $nextEntries $moreReceipts)
                 (let $all (gslt:automata:append $receipts $moreReceipts)
                   (StepAdvanced (LCons $nextEntry $nextEntries) $all)))))))))))))

(: gslt:step:round (-> Atom Atom Atom %Undefined%))
(= (gslt:step:round $plan $source $state)
   (case $state
     (((StepState $entries $log)
       (let $advanced (gslt:step:advance-all $plan $source $entries)
         (case $advanced
           (((StepAdvanced $nextEntries $receipts)
             (let $grown (gslt:automata:append $log $receipts)
               (StepState $nextEntries $grown))))))))))

(: gslt:step:rounds (-> Atom Atom Atom Atom %Undefined%))
(= (gslt:step:rounds $plan $source $work $state)
   (if (== $work 0) $state
     (let* (($next (gslt:step:round $plan $source $state))
            ($remaining (- $work 1)))
       (gslt:step:rounds $plan $source $remaining $next))))

(: gslt:step:entries-complete (-> Atom Atom %Undefined%))
(= (gslt:step:entries-complete $admitted $entries)
   (case $entries
     ((LNil True)
      ((LCons (StepEntry $job $deep) $rest)
       (let $family (gslt:step:family $admitted $job)
         (if (gslt:deep:complete $family $deep) (gslt:step:entries-complete $admitted $rest) False))))))

(: gslt:step:readout (-> Atom Atom %Undefined%))
(= (gslt:step:readout $plan $state)
   (case $plan
     (((CompletePlan $environment $permissions $bound $expected $rules $equations $admitted)
       (case $state
         (((StepState $entries $log)
           (let $complete (gslt:step:entries-complete $admitted $entries)
             (StepReadout $log $complete)))))))))

; ---------------------------------------------------------------------------
; Display erasure, contexts and positions.

(: gslt:complete:erase (-> Atom %Undefined%))
(= (gslt:complete:erase $pattern)
   (case $pattern
     (((Var $index) (Var $index))
      ((FVar $name) (FVar $name))
      ((PApp $label $arguments) (let $erased (gslt:complete:erase-list $arguments) (PApp $label $erased)))
      ((PLam $binder $body) (let $erased (gslt:complete:erase $body) (PLam BNone $erased)))
      ((PMultiLam $arity $binders $body) (let $erased (gslt:complete:erase $body) (PMultiLam $arity LNil $erased)))
      ((PSubst $body $replacement)
       (let* (($left (gslt:complete:erase $body)) ($right (gslt:complete:erase $replacement))) (PSubst $left $right)))
      ((PCollection $kind $elements $rest)
       (let $erased (gslt:complete:erase-list $elements) (PCollection $kind $erased $rest))))))

(: gslt:complete:erase-list (-> Atom %Undefined%))
(= (gslt:complete:erase-list $patterns)
   (case $patterns
     ((LNil LNil)
      ((LCons $pattern $rest)
       (let* (($head (gslt:complete:erase $pattern)) ($tail (gslt:complete:erase-list $rest))) (LCons $head $tail))))))

(: gslt:complete:binder-depth (-> Atom %Undefined%))
(= (gslt:complete:binder-depth $context)
   (case $context
     ((ContextHole 0)
      ((ContextApp $head $before $inner $after) (gslt:complete:binder-depth $inner))
      ((ContextLam $binder $inner) (let $depth (gslt:complete:binder-depth $inner) (+ 1 $depth)))
      ((ContextMultiLam $arity $binders $inner) (let $depth (gslt:complete:binder-depth $inner) (+ $arity $depth)))
      ((ContextSubstBody $inner $replacement) (let $depth (gslt:complete:binder-depth $inner) (+ 1 $depth)))
      ((ContextSubstReplacement $body $inner) (gslt:complete:binder-depth $inner))
      ((ContextCollection $kind $before $inner $after $rest) (gslt:complete:binder-depth $inner)))))

(: gslt:complete:take (-> Atom Atom %Undefined%))
(= (gslt:complete:take $count $items)
   (if (== $count 0) LNil
     (case $items
       ((LNil LNil)
        ((LCons $item $rest)
         (let* (($previous (- $count 1)) ($tail (gslt:complete:take $previous $rest))) (LCons $item $tail)))))))

(: gslt:complete:wrap (-> Atom Atom %Undefined%))
(= (gslt:complete:wrap $frame $decompositions)
   (case $decompositions
     ((LNil LNil)
      ((LCons (Decomposition $inner $focus) $rest)
       (let* (($context (gslt:complete:frame-context $frame $inner))
              ($tail (gslt:complete:wrap $frame $rest)))
         (LCons (Decomposition $context $focus) $tail))))))

(: gslt:complete:frame-context (-> Atom Atom %Undefined%))
(= (gslt:complete:frame-context $frame $inner)
   (case $frame
     (((AppFrame $head $before $after) (ContextApp $head $before $inner $after))
      ((LamFrame $binder) (ContextLam $binder $inner))
      ((MultiLamFrame $arity $binders) (ContextMultiLam $arity $binders $inner))
      ((SubstBodyFrame $replacement) (ContextSubstBody $inner $replacement))
      ((SubstReplacementFrame $body) (ContextSubstReplacement $body $inner))
      ((CollectionFrame $kind $before $after $rest) (ContextCollection $kind $before $inner $after $rest)))))

; Every position of a term, as in Complete.Predecessors.decompositions.
(: gslt:complete:decompositions (-> Atom %Undefined%))
(= (gslt:complete:decompositions $pattern)
   (let $here (Decomposition ContextHole $pattern)
     (case $pattern
       (((PApp $head $arguments)
         (let $inside (gslt:complete:argument-decompositions AppKind $head $arguments $arguments 0) (LCons $here $inside)))
        ((PLam $binder $body)
         (let* (($inner (gslt:complete:decompositions $body)) ($inside (gslt:complete:wrap (LamFrame $binder) $inner)))
           (LCons $here $inside)))
        ((PMultiLam $arity $binders $body)
         (let* (($inner (gslt:complete:decompositions $body)) ($inside (gslt:complete:wrap (MultiLamFrame $arity $binders) $inner)))
           (LCons $here $inside)))
        ((PSubst $body $replacement)
         (let* (($left (gslt:complete:decompositions $body))
                ($leftInside (gslt:complete:wrap (SubstBodyFrame $replacement) $left))
                ($right (gslt:complete:decompositions $replacement))
                ($rightInside (gslt:complete:wrap (SubstReplacementFrame $body) $right))
                ($inside (gslt:automata:append $leftInside $rightInside)))
           (LCons $here $inside)))
        ((PCollection $kind $elements $rest)
         (let $inside (gslt:complete:argument-decompositions (CollectionKind $kind $rest) $kind $elements $elements 0)
           (LCons $here $inside)))
        ($leaf (LCons $here LNil))))))

(: gslt:complete:argument-decompositions (-> Atom Atom Atom Atom Atom %Undefined%))
(= (gslt:complete:argument-decompositions $kind $head $all $remaining $index)
   (case $remaining
     ((LNil LNil)
      ((LCons $argument $rest)
       (let* (($before (gslt:complete:take $index $all))
              ($skip (+ $index 1))
              ($after (gslt:complete:drop $skip $all))
              ($frame (case $kind
                        ((AppKind (AppFrame $head $before $after))
                         ((CollectionKind $collection $tail) (CollectionFrame $collection $before $after $tail)))))
              ($inner (gslt:complete:decompositions $argument))
              ($here (gslt:complete:wrap $frame $inner))
              ($later (gslt:complete:argument-decompositions $kind $head $all $rest $skip)))
         (gslt:automata:append $here $later))))))

; ---------------------------------------------------------------------------
; The scoped matcher run to completion.

(: gslt:complete:matcher-finish (-> Atom Atom %Undefined%))
(= (gslt:complete:matcher-finish $request $state)
   (if (gslt:rule:scope-matcher-complete $state) $state
     (let $next (gslt:rule:scope-matcher-tick $request $state)
       (gslt:complete:matcher-finish $request $next))))

(: gslt:complete:matcher-answers (-> Atom %Undefined%))
(= (gslt:complete:matcher-answers $request)
   (let* (($start (gslt:rule:scope-matcher-start $request))
          ($finished (gslt:complete:matcher-finish $request $start)))
     (case $finished (((ScopedMatcherState $agenda $answers) $answers)))))

; ---------------------------------------------------------------------------
; Equation jobs (Complete.EquationJob).
;
; Plan equations: (EquationJobDeclaration position rule spec depth), rule elaborated; depth is
; (EquationDepth constant names) when the premises descend, else EquationUnbounded.
; Job: (EquationJob position rule spec site), site a RuleJobSite.
; Lane: (EquationLane job answer), answer a ScopedMatcherAnswer.
; Receipt: (EquationReceipt job trace captured completed history raw target).

(: gslt:equations:cross-sites (-> Atom Atom %Undefined%))
(= (gslt:equations:cross-sites $declaration $sites)
   (case $sites
     ((LNil LNil)
      ((LCons $site $rest)
       (let $tail (gslt:equations:cross-sites $declaration $rest)
         (case $declaration
           (((EquationJobDeclaration $position $rule $spec $depth) (LCons (EquationJob $position $rule $spec $site) $tail)))))))))

(: gslt:equations:jobs (-> Atom Atom Atom %Undefined%))
(= (gslt:equations:jobs $equations $sites $unused)
   (case $equations
     ((LNil LNil)
      ((LCons $declaration $rest)
       (let* (($here (gslt:equations:cross-sites $declaration $sites))
              ($tail (gslt:equations:jobs $rest $sites $unused)))
         (gslt:automata:append $here $tail))))))

(: gslt:equations:context (-> Atom Atom %Undefined%))
(= (gslt:equations:context $plan $job)
   (case $plan
     (((CompletePlan $environment $permissions $bound $expected $rules $equations $admitted)
       (case $job
         (((EquationJob $position $rule $spec (RuleJobSite $address $context $focus $focusBound $focusType $frames))
           (let $count (gslt:automata:length $rules) (PremiseContext $count $rule $spec $focusBound 0 0)))))))))

(: gslt:equations:typed-lanes (-> Atom Atom Atom Atom %Undefined%))
(= (gslt:equations:typed-lanes $plan $job $answers $unused)
   (case $answers
     ((LNil LNil)
      ((LCons (ScopedMatcherAnswer $assignment $trace) $rest)
       (let $tail (gslt:equations:typed-lanes $plan $job $rest $unused)
         (case $plan
           (((CompletePlan (PremiseEnvironment $declarations $rewrites $specifications $provider $reflection $free)
               $permissions $bound $expected $rules $equations $admitted)
             (case $job
               (((EquationJob $position $rule $spec (RuleJobSite $address $context $focus $focusBound $focusType $frames))
                 (if (gslt:premise:check-assignment $declarations $free $focusBound $rule $spec $assignment)
                   (LCons (EquationLane $job (ScopedMatcherAnswer $assignment $trace)) $tail)
                   $tail))))))))))))

(: gslt:equations:job-lanes (-> Atom Atom %Undefined%))
(= (gslt:equations:job-lanes $plan $job)
   (case $job
     (((EquationJob $position $rule $spec (RuleJobSite $address $context $focus $focusBound $focusType $frames))
       (case $rule
         (((ScopedRewriteRuleV1 $name $types $premises $left $right $bindings)
           (let* (($ambient (gslt:automata:length $focusBound))
                  ($erased (gslt:complete:erase $focus))
                  ($request (ScopedMatcherRequest $rule $spec $ambient RuleLeft LNil 0 LNil $left $erased))
                  ($answers (gslt:complete:matcher-answers $request)))
             (gslt:equations:typed-lanes $plan $job $answers 0)))))))))

(: gslt:equations:jobs-lanes (-> Atom Atom %Undefined%))
(= (gslt:equations:jobs-lanes $plan $jobs)
   (case $jobs
     ((LNil LNil)
      ((LCons $job $rest)
       (let* (($here (gslt:equations:job-lanes $plan $job))
              ($tail (gslt:equations:jobs-lanes $plan $rest)))
         (gslt:automata:append $here $tail))))))

; Equations are congruences: their sites are every well-sorted position, whatever reduction
; contexts the plan's rewrites have (GeneralEquationJobs.jobs).
(: gslt:equations:lanes (-> Atom Atom %Undefined%))
(= (gslt:equations:lanes $plan $source)
   (case $plan
     (((CompletePlan (PremiseEnvironment $declarations $rewrites $specifications $provider $reflection $free)
         $permissions $bound $expected $rules $equations $admitted)
       (if (gslt:premise:open-well-sorted $declarations $free $bound $expected $source)
         (let* (($sites (gslt:sites:generate $declarations $free
                   (OperationalPermissions PermissionYes PermissionYes LNil PermissionYes PermissionYes
                     (LCons "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.vec"
                       (LCons "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.hashBag"
                         (LCons "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.hashSet" LNil))))
                   $bound $expected $source))
                ($jobs (gslt:equations:jobs $equations $sites 0)))
           (gslt:equations:jobs-lanes $plan $jobs))
         LNil)))))

(: gslt:equations:family (-> Atom Atom %Undefined%))
(= (gslt:equations:family $plan $lane)
   (case $lane
     (((EquationLane $job (ScopedMatcherAnswer $assignment $trace))
       (case $job
         (((EquationJob $position $rule $spec $site)
           (case $rule
             (((ScopedRewriteRuleV1 $name $types $premises $left $right $bindings)
               (let* (($context (gslt:equations:context $plan $job))
                      ($limit (gslt:equations:limit $plan $position $assignment)))
                 (PremisesFamily $context $premises $assignment $limit))))))))))))

; The first binding of a name in an assignment (ScopedRuleMatching.lookup).
(: gslt:equations:lookup (-> Atom Atom %Undefined%))
(= (gslt:equations:lookup $name $assignment)
   (case $assignment
     ((LNil None)
      ((LCons (Binding $other $value) $rest)
       (if (== $other $name) (Some $value) (gslt:equations:lookup $name $rest))))))

; (Some total size of the captured values of the names), or None when a name is not captured.
(: gslt:equations:weight (-> Atom Atom %Undefined%))
(= (gslt:equations:weight $names $assignment)
   (case $names
     ((LNil (Some 0))
      ((LCons $name $rest)
       (let $found (gslt:equations:lookup $name $assignment)
         (case $found
           ((None None)
            ((Some (ContextualValue $dependencies $ambient $body))
             (let $tail (gslt:equations:weight $rest $assignment)
               (case $tail
                 ((None None)
                  ((Some $sum) (let $size (gslt:deep:nodes $body) (Some (+ $size $sum)))))))))))))))

(: gslt:equations:declared-depth (-> Atom Atom %Undefined%))
(= (gslt:equations:declared-depth $position $equations)
   (case $equations
     ((LNil EquationUnbounded)
      ((LCons (EquationJobDeclaration $other $rule $spec $depth) $rest)
       (if (== $other $position) $depth (gslt:equations:declared-depth $position $rest))))))

; The depth every premise derivation of the job at the capture fits in (EquationJob.premisesBound).
(: gslt:equations:limit (-> Atom Atom Atom %Undefined%))
(= (gslt:equations:limit $plan $position $assignment)
   (case $plan
     (((CompletePlan $environment $permissions $bound $expected $rules $equations $admitted)
       (let $depth (gslt:equations:declared-depth $position $equations)
         (case $depth
           ((EquationUnbounded None)
            ((EquationDepth $constant $names)
             (let $weight (gslt:equations:weight $names $assignment)
               (case $weight
                 ((None None)
                  ((Some $sum) (Some (+ $constant $sum))))))))))))))

; A premise outcome finished by the job's local checks (GeneralEquationJobs.finish).
(: gslt:equations:lift (-> Atom Atom Atom %Undefined%))
(= (gslt:equations:lift $plan $lane $outcome)
   (case $plan
     (((CompletePlan (PremiseEnvironment $declarations $rewrites $specifications $provider $reflection $free)
         $permissions $bound $expected $rules $equations $admitted)
       (case $lane
         (((EquationLane (EquationJob $position $rule $spec (RuleJobSite $address $context $focus $focusBound $focusType $frames))
             (ScopedMatcherAnswer $captured $trace))
           (case $outcome
             (((PremisesAnswer $completed $history)
               (if (gslt:premise:check-assignment $declarations $free $focusBound $rule $spec $captured)
                 (if (gslt:premise:check-assignment $declarations $free $focusBound $rule $spec $completed)
                   (let $ambient (gslt:automata:length $focusBound)
                     (case (gslt:rule:scope-reduct None $rule $spec $ambient $completed)
                       ((None None)
                        ((Some $raw)
                         (let $local (gslt:complete:erase $raw)
                           (if (gslt:rule:site-replacement-represented $declarations $context $frames $local)
                             (if (gslt:premise:open-well-sorted $declarations $free $focusBound $focusType $local)
                               (let* (($filled (gslt:rule:scope-fill $context $local))
                                      ($target (gslt:complete:erase $filled)))
                                 (if (gslt:premise:open-well-sorted $declarations $free $bound $expected $target)
                                   (Some (EquationReceipt
                                     (EquationJob $position $rule $spec (RuleJobSite $address $context $focus $focusBound $focusType $frames))
                                     $trace $captured $completed $history $raw $target))
                                   None))
                               None)
                             None))))))
                   None)
                 None)))))))))))

; ---------------------------------------------------------------------------
; Predecessors (Complete.Predecessors), and every order of a list (Inversion.perms).

(: gslt:complete:insertions (-> Atom Atom %Undefined%))
(= (gslt:complete:insertions $item $items)
   (case $items
     ((LNil (LCons (LCons $item LNil) LNil))
      ((LCons $first $rest)
       (let* (($inner (gslt:complete:insertions $item $rest))
              ($shifted (gslt:complete:cons-each $first $inner)))
         (LCons (LCons $item (LCons $first $rest)) $shifted))))))

(: gslt:complete:cons-each (-> Atom Atom %Undefined%))
(= (gslt:complete:cons-each $item $lists)
   (case $lists
     ((LNil LNil)
      ((LCons $list $rest)
       (let $tail (gslt:complete:cons-each $item $rest) (LCons (LCons $item $list) $tail))))))

(: gslt:complete:perms (-> Atom %Undefined%))
(= (gslt:complete:perms $items)
   (case $items
     ((LNil (LCons LNil LNil))
      ((LCons $first $rest)
       (let $orders (gslt:complete:perms $rest) (gslt:complete:insert-all $first $orders))))))

(: gslt:complete:insert-all (-> Atom Atom %Undefined%))
(= (gslt:complete:insert-all $item $orders)
   (case $orders
     ((LNil LNil)
      ((LCons $order $rest)
       (let* (($here (gslt:complete:insertions $item $order))
              ($tail (gslt:complete:insert-all $item $rest)))
         (gslt:automata:append $here $tail))))))

(: gslt:complete:perms-all (-> Atom %Undefined%))
(= (gslt:complete:perms-all $lists)
   (case $lists
     ((LNil LNil)
      ((LCons $list $rest)
       (let* (($here (gslt:complete:perms $list)) ($tail (gslt:complete:perms-all $rest)))
         (gslt:automata:append $here $tail))))))

(: gslt:complete:wrap-each (-> Atom Atom %Undefined%))
(= (gslt:complete:wrap-each $shape $lists)
   (case $lists
     ((LNil LNil)
      ((LCons $list $rest)
       (let* (($tail (gslt:complete:wrap-each $shape $rest))
              ($built (case $shape
                        (((ApplyShape $label) (PApp $label $list))
                         ((CollectionShape $kind) (PCollection $kind $list RNone))))))
         (LCons $built $tail))))))

; The display-erased terms an instance of a side can stand for (Inversion.variants).
(: gslt:complete:variants (-> Atom Atom %Undefined%))
(= (gslt:complete:variants $schema $instance)
   (case (VariantPair $schema $instance)
     (((VariantPair (PApp $schemaLabel $patterns) (PApp $label $targets))
       (let* (($rows (gslt:complete:variants-list $patterns $targets)))
         (gslt:complete:wrap-each (ApplyShape $label) $rows)))
      ((VariantPair (PLam $schemaBinder $pattern) (PLam $binder $target))
       (let $inner (gslt:complete:variants $pattern $target) (gslt:complete:lambda-each $inner)))
      ((VariantPair (PMultiLam $schemaArity $schemaBinders $pattern) (PMultiLam $arity $binders $target))
       (let $inner (gslt:complete:variants $pattern $target) (gslt:complete:multi-lambda-each $arity $inner)))
      ((VariantPair (PCollection $kind $patterns RNone) (PCollection $actual $targets RNone))
       (let $rows (gslt:complete:variants-list $patterns $targets)
         (if (== $kind "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.vec")
           (gslt:complete:wrap-each (CollectionShape $actual) $rows)
           (let $orders (gslt:complete:perms-all $rows) (gslt:complete:wrap-each (CollectionShape $actual) $orders)))))
      ((VariantPair (PCollection $kind $patterns (RSome $restName)) (PCollection $actual $targets RNone))
       (let* (($count (gslt:automata:length $patterns))
              ($front (gslt:complete:take $count $targets))
              ($remaining (gslt:complete:drop $count $targets))
              ($back (gslt:complete:erase-list $remaining))
              ($rows (gslt:complete:variants-list $patterns $front))
              ($joined (gslt:complete:append-each $rows $back)))
         (if (== $kind "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.vec")
           (gslt:complete:wrap-each (CollectionShape $actual) $joined)
           (let $orders (gslt:complete:perms-all $joined) (gslt:complete:wrap-each (CollectionShape $actual) $orders)))))
      ($other (let $erased (gslt:complete:erase $instance) (LCons $erased LNil))))))

; Every row followed by the same tail.
(: gslt:complete:append-each (-> Atom Atom %Undefined%))
(= (gslt:complete:append-each $rows $back)
   (case $rows
     ((LNil LNil)
      ((LCons $row $rest)
       (let* (($joined (gslt:automata:append $row $back))
              ($tail (gslt:complete:append-each $rest $back)))
         (LCons $joined $tail))))))

(: gslt:complete:lambda-each (-> Atom %Undefined%))
(= (gslt:complete:lambda-each $bodies)
   (case $bodies
     ((LNil LNil)
      ((LCons $body $rest) (let $tail (gslt:complete:lambda-each $rest) (LCons (PLam BNone $body) $tail))))))

(: gslt:complete:multi-lambda-each (-> Atom Atom %Undefined%))
(= (gslt:complete:multi-lambda-each $arity $bodies)
   (case $bodies
     ((LNil LNil)
      ((LCons $body $rest)
       (let $tail (gslt:complete:multi-lambda-each $arity $rest) (LCons (PMultiLam $arity LNil $body) $tail))))))

(: gslt:complete:variants-list (-> Atom Atom %Undefined%))
(= (gslt:complete:variants-list $patterns $targets)
   (case (VariantPair $patterns $targets)
     (((VariantPair LNil LNil) (LCons LNil LNil))
      ((VariantPair (LCons $pattern $patternRest) (LCons $target $targetRest))
       (let* (($heads (gslt:complete:variants $pattern $target))
              ($tails (gslt:complete:variants-list $patternRest $targetRest)))
         (gslt:complete:product $heads $tails)))
      ($mismatch LNil))))

(: gslt:complete:product (-> Atom Atom %Undefined%))
(= (gslt:complete:product $heads $tails)
   (case $heads
     ((LNil LNil)
      ((LCons $head $rest)
       (let* (($here (gslt:complete:cons-each $head $tails))
              ($later (gslt:complete:product $rest $tails)))
         (gslt:automata:append $here $later))))))

(: gslt:complete:fill-each (-> Atom Atom %Undefined%))
(= (gslt:complete:fill-each $context $sources)
   (case $sources
     ((LNil LNil)
      ((LCons $source $rest)
       (let* (($filled (gslt:rule:scope-fill $context $source))
              ($erased (gslt:complete:erase $filled))
              ($tail (gslt:complete:fill-each $context $rest)))
         (LCons $erased $tail))))))

(: gslt:complete:candidates-from (-> Atom Atom Atom Atom Atom %Undefined%))
(= (gslt:complete:candidates-from $rule $spec $ambient $context $answers)
   (case $answers
     ((LNil LNil)
      ((LCons (ScopedMatcherAnswer $captures $trace) $rest)
       (let $tail (gslt:complete:candidates-from $rule $spec $ambient $context $rest)
         (case $rule
           (((ScopedRewriteRuleV1 $name $types $premises $left $right $bindings)
             (case (gslt:rule:scope-instantiate-at None $rule $spec $ambient RuleLeft LNil 0 $captures $left)
               ((None $tail)
                ((Some $instance)
                 (let* (($sources (gslt:complete:variants $left $instance))
                        ($filled (gslt:complete:fill-each $context $sources)))
                   (gslt:automata:append $filled $tail)))))))))))))

(: gslt:complete:equation-candidates (-> Atom Atom Atom Atom %Undefined%))
(= (gslt:complete:equation-candidates $equations $ambient $context $focus)
   (case $equations
     ((LNil LNil)
      ((LCons (EquationJobDeclaration $position $rule $spec $depth) $rest)
       (let $tail (gslt:complete:equation-candidates $rest $ambient $context $focus)
         (case $rule
           (((ScopedRewriteRuleV1 $name $types $premises $left $right $bindings)
             (let* (($request (ScopedMatcherRequest $rule $spec $ambient RuleRight LNil 0 LNil $right $focus))
                    ($answers (gslt:complete:matcher-answers $request))
                    ($here (gslt:complete:candidates-from $rule $spec $ambient $context $answers)))
               (gslt:automata:append $here $tail))))))))))

(: gslt:complete:predecessors-from (-> Atom Atom Atom %Undefined%))
(= (gslt:complete:predecessors-from $plan $bound $decompositions)
   (case $decompositions
     ((LNil LNil)
      ((LCons (Decomposition $context $focus) $rest)
       (case $plan
         (((CompletePlan $environment $permissions $planBound $expected $rules $equations $admitted)
           (let* (($outer (gslt:automata:length $bound))
                  ($inner (gslt:complete:binder-depth $context))
                  ($ambient (+ $outer $inner))
                  ($here (gslt:complete:equation-candidates $equations $ambient $context $focus))
                  ($tail (gslt:complete:predecessors-from $plan $bound $rest)))
             (gslt:automata:append $here $tail)))))))))

(: gslt:complete:predecessors (-> Atom Atom %Undefined%))
(= (gslt:complete:predecessors $plan $target)
   (case $plan
     (((CompletePlan $environment $permissions $bound $expected $rules $equations $admitted)
       (if (== $equations LNil) LNil
         (let $decompositions (gslt:complete:decompositions $target)
           (gslt:complete:predecessors-from $plan $bound $decompositions)))))))

; ---------------------------------------------------------------------------
; Steps modulo equations (Complete.Classes).
;
; Rep: (ClassRep pattern conversions born).
; Keys: (RuleKey rep job), (ForwardKey rep lane), (BackwardKey rep candidate lane).
; Entry: (ClassEntry key deep). State: (ClassState round reps entries log).
; Events: (FiringEvent receipt), (DiscoveryEvent pattern conversions).
; Published receipt: (ClassReceipt representative conversions firing).

(: gslt:classes:family (-> Atom Atom %Undefined%))
(= (gslt:classes:family $plan $key)
   (case $key
     (((RuleKey $rep $job)
       (case $plan (((CompletePlan $environment $permissions $bound $expected $rules $equations $admitted)
         (gslt:step:family $admitted $job)))))
      ((ForwardKey $rep $lane) (gslt:equations:family $plan $lane))
      ((BackwardKey $rep $candidate $lane) (gslt:equations:family $plan $lane)))))

(: gslt:classes:forward-events (-> Atom Atom Atom Atom %Undefined%))
(= (gslt:classes:forward-events $plan $conversions $lane $payloads)
   (case $payloads
     ((LNil LNil)
      ((LCons $payload $rest)
       (let* (($lifted (gslt:equations:lift $plan $lane $payload))
              ($tail (gslt:classes:forward-events $plan $conversions $lane $rest)))
         (case $lifted
           ((None $tail)
            ((Some (EquationReceipt $job $trace $captured $completed $history $raw $target))
             (let $path (gslt:automata:append $conversions
                          (LCons (ForwardConversion (EquationReceipt $job $trace $captured $completed $history $raw $target)) LNil))
               (LCons (DiscoveryEvent $target $path) $tail))))))))))

(: gslt:classes:backward-events (-> Atom Atom Atom Atom Atom Atom %Undefined%))
(= (gslt:classes:backward-events $plan $pattern $conversions $candidate $lane $payloads)
   (case $payloads
     ((LNil LNil)
      ((LCons $payload $rest)
       (let* (($lifted (gslt:equations:lift $plan $lane $payload))
              ($tail (gslt:classes:backward-events $plan $pattern $conversions $candidate $lane $rest)))
         (case $lifted
           ((None $tail)
            ((Some (EquationReceipt $job $trace $captured $completed $history $raw $target))
             (if (== $target $pattern)
               (let $path (gslt:automata:append $conversions
                            (LCons (ReverseConversion (EquationReceipt $job $trace $captured $completed $history $raw $target)) LNil))
                 (LCons (DiscoveryEvent $candidate $path) $tail))
               $tail)))))))))

(: gslt:classes:firing-events (-> Atom Atom Atom %Undefined%))
(= (gslt:classes:firing-events $pattern $conversions $receipts)
   (case $receipts
     ((LNil LNil)
      ((LCons $receipt $rest)
       (let $tail (gslt:classes:firing-events $pattern $conversions $rest)
         (LCons (FiringEvent (ClassReceipt $pattern $conversions $receipt)) $tail))))))

(: gslt:classes:events (-> Atom Atom Atom %Undefined%))
(= (gslt:classes:events $plan $key $payloads)
   (case $key
     (((RuleKey (ClassRep $pattern $conversions $born) $job)
       (case $plan (((CompletePlan $environment $permissions $bound $expected $rules $equations $admitted)
         (let $receipts (gslt:step:lift $plan $pattern $job $payloads $permissions)
           (gslt:classes:firing-events $pattern $conversions $receipts))))))
      ((ForwardKey (ClassRep $pattern $conversions $born) $lane)
       (gslt:classes:forward-events $plan $conversions $lane $payloads))
      ((BackwardKey (ClassRep $pattern $conversions $born) $candidate $lane)
       (gslt:classes:backward-events $plan $pattern $conversions $candidate $lane $payloads)))))

(: gslt:classes:keys (-> Atom Atom Atom %Undefined%))
(= (gslt:classes:keys $kind $rep $items)
   (case $items
     ((LNil LNil)
      ((LCons $item $rest)
       (let $tail (gslt:classes:keys $kind $rep $rest)
         (case $kind
           ((RuleKind (LCons (RuleKey $rep $item) $tail))
            (ForwardKind (LCons (ForwardKey $rep $item) $tail))
            ((BackwardKind $candidate) (LCons (BackwardKey $rep $candidate $item) $tail)))))))))

(: gslt:classes:backward-keys (-> Atom Atom Atom %Undefined%))
(= (gslt:classes:backward-keys $plan $rep $candidates)
   (case $candidates
     ((LNil LNil)
      ((LCons $candidate $rest)
       (let* (($lanes (gslt:equations:lanes $plan $candidate))
              ($here (gslt:classes:keys (BackwardKind $candidate) $rep $lanes))
              ($tail (gslt:classes:backward-keys $plan $rep $rest)))
         (gslt:automata:append $here $tail))))))

(: gslt:classes:lanes (-> Atom Atom %Undefined%))
(= (gslt:classes:lanes $plan $rep)
   (case $plan
     (((CompletePlan (PremiseEnvironment $declarations $rewrites $specifications $provider $reflection $free)
         $permissions $bound $expected $rules $equations $admitted)
       (case $rep
         (((ClassRep $pattern $conversions $born)
           (let* (($jobs (gslt:sites:jobs $declarations $free $permissions $bound $expected $pattern $rules))
                  ($ruleKeys (gslt:classes:keys RuleKind $rep $jobs))
                  ($forward (gslt:equations:lanes $plan $pattern))
                  ($forwardKeys (gslt:classes:keys ForwardKind $rep $forward))
                  ($candidates (gslt:complete:predecessors $plan $pattern))
                  ($backwardKeys (gslt:classes:backward-keys $plan $rep $candidates))
                  ($early (gslt:automata:append $ruleKeys $forwardKeys)))
             (gslt:automata:append $early $backwardKeys)))))))))

(: gslt:classes:start-entries (-> Atom Atom %Undefined%))
(= (gslt:classes:start-entries $plan $keys)
   (case $keys
     ((LNil LNil)
      ((LCons $key $rest)
       (let* (($family (gslt:classes:family $plan $key))
              ($deep (gslt:deep:start $family))
              ($tail (gslt:classes:start-entries $plan $rest)))
         (LCons (ClassEntry $key $deep) $tail))))))

(: gslt:classes:reps-lanes (-> Atom Atom %Undefined%))
(= (gslt:classes:reps-lanes $plan $reps)
   (case $reps
     ((LNil LNil)
      ((LCons $rep $rest)
       (let* (($here (gslt:classes:lanes $plan $rep)) ($tail (gslt:classes:reps-lanes $plan $rest)))
         (gslt:automata:append $here $tail))))))

(: gslt:classes:begin (-> Atom Atom %Undefined%))
(= (gslt:classes:begin $plan $source)
   (let* (($rep (ClassRep $source LNil 0))
          ($keys (gslt:classes:lanes $plan $rep))
          ($entries (gslt:classes:start-entries $plan $keys)))
     (ClassState 0 (LCons $rep LNil) $entries LNil)))

(: gslt:classes:advance (-> Atom Atom %Undefined%))
(= (gslt:classes:advance $plan $entry)
   (case $plan
     (((CompletePlan $environment $permissions $bound $expected $rules $equations $admitted)
       (case $entry
         (((ClassEntry $key $deep)
           (let* (($family (gslt:classes:family $plan $key))
                  ($before (gslt:deep:publication $deep))
                  ($count (gslt:automata:length $before))
                  ($next (gslt:deep:tick $environment $family $deep))
                  ($after (gslt:deep:publication $next))
                  ($new (gslt:complete:drop $count $after))
                  ($events (gslt:classes:events $plan $key $new)))
             (ClassAdvanced (ClassEntry $key $next) $events)))))))))

(: gslt:classes:advance-all (-> Atom Atom %Undefined%))
(= (gslt:classes:advance-all $plan $entries)
   (case $entries
     ((LNil (ClassAdvanced LNil LNil))
      ((LCons $entry $rest)
       (let* (($head (gslt:classes:advance $plan $entry))
              ($tail (gslt:classes:advance-all $plan $rest)))
         (case $head
           (((ClassAdvanced $nextEntry $events)
             (case $tail
               (((ClassAdvanced $nextEntries $moreEvents)
                 (let $all (gslt:automata:append $events $moreEvents)
                   (ClassAdvanced (LCons $nextEntry $nextEntries) $all)))))))))))))

(: gslt:classes:represented (-> Atom Atom %Undefined%))
(= (gslt:classes:represented $pattern $reps)
   (case $reps
     ((LNil False)
      ((LCons (ClassRep $other $conversions $born) $rest)
       (if (== $other $pattern) True (gslt:classes:represented $pattern $rest))))))

(: gslt:classes:add-discoveries (-> Atom Atom Atom %Undefined%))
(= (gslt:classes:add-discoveries $born $reps $events)
   (case $events
     ((LNil $reps)
      ((LCons (FiringEvent $receipt) $rest) (gslt:classes:add-discoveries $born $reps $rest))
      ((LCons (DiscoveryEvent $pattern $conversions) $rest)
       (if (gslt:classes:represented $pattern $reps)
         (gslt:classes:add-discoveries $born $reps $rest)
         (let $grown (gslt:automata:append $reps (LCons (ClassRep $pattern $conversions $born) LNil))
           (gslt:classes:add-discoveries $born $grown $rest)))))))

(: gslt:classes:firings (-> Atom %Undefined%))
(= (gslt:classes:firings $events)
   (case $events
     ((LNil LNil)
      ((LCons (FiringEvent $receipt) $rest) (let $tail (gslt:classes:firings $rest) (LCons $receipt $tail)))
      ((LCons (DiscoveryEvent $pattern $conversions) $rest) (gslt:classes:firings $rest)))))

(: gslt:classes:round (-> Atom Atom %Undefined%))
(= (gslt:classes:round $plan $state)
   (case $state
     (((ClassState $round $reps $entries $log)
       (let $advanced (gslt:classes:advance-all $plan $entries)
         (case $advanced
           (((ClassAdvanced $nextEntries $events)
             (let* (($born (+ $round 1))
                    ($grown (gslt:classes:add-discoveries $born $reps $events))
                    ($count (gslt:automata:length $reps))
                    ($new (gslt:complete:drop $count $grown))
                    ($keys (gslt:classes:reps-lanes $plan $new))
                    ($fresh (gslt:classes:start-entries $plan $keys))
                    ($all (gslt:automata:append $nextEntries $fresh))
                    ($firings (gslt:classes:firings $events))
                    ($published (gslt:automata:append $log $firings)))
               (ClassState $born $grown $all $published))))))))))

(: gslt:classes:rounds (-> Atom Atom Atom %Undefined%))
(= (gslt:classes:rounds $plan $work $state)
   (if (== $work 0) $state
     (let* (($next (gslt:classes:round $plan $state))
            ($remaining (- $work 1)))
       (gslt:classes:rounds $plan $remaining $next))))

(: gslt:classes:entries-complete (-> Atom Atom %Undefined%))
(= (gslt:classes:entries-complete $plan $entries)
   (case $entries
     ((LNil True)
      ((LCons (ClassEntry $key $deep) $rest)
       (let $family (gslt:classes:family $plan $key)
         (if (gslt:deep:complete $family $deep) (gslt:classes:entries-complete $plan $rest) False))))))

(: gslt:classes:patterns (-> Atom %Undefined%))
(= (gslt:classes:patterns $reps)
   (case $reps
     ((LNil LNil)
      ((LCons (ClassRep $pattern $conversions $born) $rest)
       (let $tail (gslt:classes:patterns $rest) (LCons $pattern $tail))))))

(: gslt:classes:readout (-> Atom Atom %Undefined%))
(= (gslt:classes:readout $plan $state)
   (case $state
     (((ClassState $round $reps $entries $log)
       (let* (($patterns (gslt:classes:patterns $reps))
              ($complete (gslt:classes:entries-complete $plan $entries)))
         (ClassReadout $patterns $log $complete))))))

; The premise limit of every equation lane (EquationJob.premisesBound), in lane order.
(: gslt:equations:lane-limits (-> Atom Atom %Undefined%))
(= (gslt:equations:lane-limits $plan $lanes)
   (case $lanes
     ((LNil LNil)
      ((LCons (EquationLane (EquationJob $position $rule $spec $site) (ScopedMatcherAnswer $assignment $trace)) $rest)
       (let* (($limit (gslt:equations:limit $plan $position $assignment))
              ($tail (gslt:equations:lane-limits $plan $rest)))
         (LCons $limit $tail))))))
