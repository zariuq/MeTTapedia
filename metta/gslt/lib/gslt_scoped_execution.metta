; Shared first-order subterm matching. Inputs use the canonical LanguageDef
; Pattern wire: FVar, Var, PApp, LNil/LCons. Authored rows stay ordered and
; duplicate rows retain distinct indices. Structural automata only select
; candidates; one binding continuation checks repeated variables.
; The top-down realization uses shared position observations and derivatives.
; The bottom-up realization interns subpatterns and shares child match states.

(: gslt:automata:append (-> Atom Atom %Undefined%))
(= (gslt:automata:append $left $right)
   (case $left
     ((LNil $right)
      ((LCons $x $xs) (let $tail (gslt:automata:append $xs $right) (LCons $x $tail))))))
(: gslt:automata:length (-> Atom %Undefined%))
(= (gslt:automata:length $xs)
   (case $xs ((LNil 0) ((LCons $x $rest) (+ 1 (gslt:automata:length $rest))))))
(: gslt:automata:member (-> Atom Atom %Undefined%))
(= (gslt:automata:member $x $xs)
   (case $xs ((LNil False) ((LCons $y $rest)
     (if (== $x $y) True (gslt:automata:member $x $rest))))))
(: gslt:automata:unique (-> Atom %Undefined%))
(= (gslt:automata:unique $xs) (gslt:automata:unique-acc $xs LNil))
(: gslt:automata:unique-acc (-> Atom Atom %Undefined%))
(= (gslt:automata:unique-acc $xs $seen)
   (case $xs
     ((LNil LNil)
      ((LCons $x $rest)
       (if (gslt:automata:member $x $seen) (gslt:automata:unique-acc $rest $seen)
         (let* (($seen-next (LCons $x $seen))
                ($tail (gslt:automata:unique-acc $rest $seen-next))) (LCons $x $tail)))))))

; Shapes are compiled instructions, not a second source term format.
(: gslt:automata:shape (-> Atom %Undefined%))
(= (gslt:automata:shape $p)
   (case $p
     (((FVar $name) MAny)
      ((Var $index) (MNode (HBound $index) LNil))
      ((PApp $head $children)
       (let* (($arity (gslt:automata:length $children))
              ($shapes (gslt:automata:shapes $children)))
         (MNode (HApp $head $arity) $shapes))))))
(: gslt:automata:shapes (-> Atom %Undefined%))
(= (gslt:automata:shapes $ps)
   (case $ps ((LNil LNil) ((LCons $p $rest)
     (let* (($head (gslt:automata:shape $p)) ($tail (gslt:automata:shapes $rest)))
       (LCons $head $tail))))))
(: gslt:automata:subject (-> Atom %Undefined%))
(= (gslt:automata:subject $p)
   (case $p
     (((FVar $name) (MNode (HFree $name) LNil))
      ((Var $index) (MNode (HBound $index) LNil))
      ((PApp $head $children)
       (let* (($arity (gslt:automata:length $children))
              ($subjects (gslt:automata:subjects $children)))
         (MNode (HApp $head $arity) $subjects))))))
(: gslt:automata:subjects (-> Atom %Undefined%))
(= (gslt:automata:subjects $ps)
   (case $ps ((LNil LNil) ((LCons $p $rest)
     (let* (($head (gslt:automata:subject $p)) ($tail (gslt:automata:subjects $rest)))
       (LCons $head $tail))))))
(: gslt:automata:subpatterns (-> Atom %Undefined%))
(= (gslt:automata:subpatterns $p)
   (case $p
     ((MAny (LCons MAny LNil))
      ((MNode $head $children)
       (let $rest (gslt:automata:subpatterns-list $children) (LCons $p $rest))))))
(: gslt:automata:subpatterns-list (-> Atom %Undefined%))
(= (gslt:automata:subpatterns-list $ps)
   (case $ps ((LNil LNil) ((LCons $p $rest)
     (let* (($head (gslt:automata:subpatterns $p))
            ($tail (gslt:automata:subpatterns-list $rest)))
       (gslt:automata:append $head $tail))))))

(: gslt:automata:child-accept (-> Atom Atom %Undefined%))
(= (gslt:automata:child-accept $patterns $states)
   (case ($patterns $states)
     (((LNil LNil) True)
      (((LCons $p $ps) (LCons (MState $matches $children $reads $tests) $ss))
       (if (gslt:automata:member $p $matches) (gslt:automata:child-accept $ps $ss) False))
      ($bad False))))
(: gslt:automata:accept (-> Atom Atom Atom %Undefined%))
(= (gslt:automata:accept $head $states $pattern)
   (case $pattern ((MAny True) ((MNode $expected $children)
     (if (== $head $expected) (gslt:automata:child-accept $children $states) False)))))
(: gslt:automata:transition (-> Atom Atom Atom %Undefined%))
(= (gslt:automata:transition $inventory $head $states)
   (case $inventory ((LNil LNil) ((LCons $p $ps)
     (let $tail (gslt:automata:transition $ps $head $states)
       (if (gslt:automata:accept $head $states $p) (LCons $p $tail) $tail))))))
(: gslt:automata:bottom-state (-> Atom Atom %Undefined%))
(= (gslt:automata:bottom-state $inventory (MNode $head $children))
   (let* (($states (gslt:automata:bottom-states $inventory $children))
          ($matches (gslt:automata:transition $inventory $head $states))
          ($counts (gslt:automata:state-counts $states))
          ($tests (gslt:automata:length $inventory)))
     (case $counts (((Counts $reads $child-tests)
       (MState $matches $states (+ 1 $reads) (+ $tests $child-tests)))))))
(: gslt:automata:bottom-states (-> Atom Atom %Undefined%))
(= (gslt:automata:bottom-states $inventory $children)
   (case $children ((LNil LNil) ((LCons $child $rest)
     (let* (($head (gslt:automata:bottom-state $inventory $child))
            ($tail (gslt:automata:bottom-states $inventory $rest))) (LCons $head $tail))))))
(: gslt:automata:state-counts (-> Atom %Undefined%))
(= (gslt:automata:state-counts $states)
   (case $states ((LNil (Counts 0 0))
     ((LCons (MState $matches $children $reads $tests) $rest)
      (case (gslt:automata:state-counts $rest)
        (((Counts $tail-reads $tail-tests) (Counts (+ $reads $tail-reads) (+ $tests $tail-tests)))))))))
(: gslt:automata:select (-> Atom Atom Atom Number %Undefined%))
(= (gslt:automata:select $patterns $matches $path $next)
   (case $patterns ((LNil LNil) ((LCons $p $ps)
     (let $tail (gslt:automata:select $ps $matches $path (+ $next 1))
       (if (gslt:automata:member $p $matches) (LCons (At $path $next) $tail) $tail))))))
(: gslt:automata:bottom-locations (-> Atom Atom Atom %Undefined%))
(= (gslt:automata:bottom-locations $patterns (MState $matches $children $reads $tests) $path)
   (let* (($here (gslt:automata:select $patterns $matches $path 0))
          ($below (gslt:automata:bottom-locations-list $patterns $children $path 0)))
     (gslt:automata:append $here $below)))
(: gslt:automata:bottom-locations-list (-> Atom Atom Atom Number %Undefined%))
(= (gslt:automata:bottom-locations-list $patterns $children $path $next)
   (case $children ((LNil LNil) ((LCons $child $rest)
     (let* (($child-path (gslt:automata:append $path (LCons $next LNil)))
            ($head (gslt:automata:bottom-locations $patterns $child $child-path))
            ($tail (gslt:automata:bottom-locations-list $patterns $rest $path (+ $next 1))))
       (gslt:automata:append $head $tail))))))

; Top-down compiled constructor obligations and shared position observations.
(: gslt:automata:compile (-> Atom Atom %Undefined%))
(= (gslt:automata:compile $pattern $path)
   (case $pattern ((MAny LNil) ((MNode $head $children)
     (let* (($arity (gslt:automata:length $children))
            ($tail (gslt:automata:compile-children $children $path 0)))
       (LCons (Observe $path (MKey $head $arity)) $tail))))))
(: gslt:automata:compile-children (-> Atom Atom Number %Undefined%))
(= (gslt:automata:compile-children $children $path $next)
   (case $children ((LNil LNil) ((LCons $child $rest)
     (let* (($child-path (gslt:automata:append $path (LCons $next LNil)))
            ($head (gslt:automata:compile $child $child-path))
            ($tail (gslt:automata:compile-children $rest $path (+ $next 1))))
       (gslt:automata:append $head $tail))))))
(: gslt:automata:programs (-> Atom %Undefined%))
(= (gslt:automata:programs $patterns)
   (case $patterns ((LNil LNil) ((LCons $p $ps)
     (let* (($head (gslt:automata:compile $p LNil))
            ($tail (gslt:automata:programs $ps))) (LCons $head $tail))))))
(: gslt:automata:observe (-> Atom Atom %Undefined%))
(= (gslt:automata:observe (MNode $head $children) $path)
   (let* (($arity (gslt:automata:length $children))
          ($tail (gslt:automata:observe-children $children $path 0)))
     (LCons (Observe $path (MKey $head $arity)) $tail)))
(: gslt:automata:observe-children (-> Atom Atom Number %Undefined%))
(= (gslt:automata:observe-children $children $path $next)
   (case $children ((LNil LNil) ((LCons $child $rest)
     (let* (($child-path (gslt:automata:append $path (LCons $next LNil)))
            ($head (gslt:automata:observe $child $child-path))
            ($tail (gslt:automata:observe-children $rest $path (+ $next 1))))
       (gslt:automata:append $head $tail))))))
(: gslt:automata:shift (-> Atom Atom %Undefined%))
(= (gslt:automata:shift $root $obligations)
   (case $obligations ((LNil LNil) ((LCons (Observe $path $key) $rest)
     (let* (($position (gslt:automata:append $root $path))
            ($tail (gslt:automata:shift $root $rest)))
       (LCons (Observe $position $key) $tail))))))
(: gslt:automata:seed (-> Atom Atom Number %Undefined%))
(= (gslt:automata:seed $root $programs $next)
   (case $programs ((LNil LNil) ((LCons $program $rest)
     (let* (($pending (gslt:automata:shift $root $program))
            ($tail (gslt:automata:seed $root $rest (+ $next 1))))
       (LCons (MGoal (At $root $next) $pending) $tail))))))
(: gslt:automata:seed-all (-> Atom Atom %Undefined%))
(= (gslt:automata:seed-all $observations $programs)
   (case $observations ((LNil LNil) ((LCons (Observe $root $key) $rest)
     (let* (($head (gslt:automata:seed $root $programs 0))
            ($tail (gslt:automata:seed-all $rest $programs)))
       (gslt:automata:append $head $tail))))))
(: gslt:automata:derive (-> Atom Atom %Undefined%))
(= (gslt:automata:derive (Observe $position $key) $pending)
   (case $pending
     ((LNil (Some LNil))
      ((LCons (Observe $expected-position $expected-key) $rest)
       (if (== $position $expected-position)
         (if (== $key $expected-key) (gslt:automata:derive (Observe $position $key) $rest) None)
         (case (gslt:automata:derive (Observe $position $key) $rest)
           (((Some $tail) (Some (LCons (Observe $expected-position $expected-key) $tail)))
            (None None))))))))
(: gslt:automata:derive-goals (-> Atom Atom %Undefined%))
(= (gslt:automata:derive-goals $observation $goals)
   (case $goals ((LNil LNil) ((LCons (MGoal $location $pending) $rest)
     (let $tail (gslt:automata:derive-goals $observation $rest)
       (case (gslt:automata:derive $observation $pending)
         (((Some $remaining) (LCons (MGoal $location $remaining) $tail))
          (None $tail))))))))
(: gslt:automata:execute (-> Atom Atom Number %Undefined%))
(= (gslt:automata:execute $observations $goals $dispatches)
   (case $observations
     ((LNil (MFinished $goals $dispatches))
      ((LCons $observation $rest)
       (let* (($count (gslt:automata:length $goals))
              ($next (gslt:automata:derive-goals $observation $goals)))
         (gslt:automata:execute $rest $next (+ $dispatches $count)))))))
(: gslt:automata:completed (-> Atom %Undefined%))
(= (gslt:automata:completed $goals)
   (case $goals ((LNil LNil) ((LCons (MGoal $location $pending) $rest)
     (let $tail (gslt:automata:completed $rest)
       (if (== $pending LNil) (LCons $location $tail) $tail))))))

; One canonical binding continuation is shared by both structural machines.
; Merge folds the right binding list into the left, just as Lean mergeBindings.
(: gslt:automata:binding (-> Atom Atom %Undefined%))
(= (gslt:automata:binding $name $bindings)
   (case $bindings ((LNil None) ((LCons (Binding $key $value) $rest)
     (if (== $name $key) (Some $value) (gslt:automata:binding $name $rest))))))
(: gslt:automata:merge (-> Atom Atom %Undefined%))
(= (gslt:automata:merge $left $right)
   (case $right
     ((LNil (Some $left))
      ((LCons (Binding $name $value) $rest)
       (case (gslt:automata:binding $name $left)
         ((None (let $next (LCons (Binding $name $value) $left) (gslt:automata:merge $next $rest)))
          ((Some $found) (if (== $found $value) (gslt:automata:merge $left $rest) None))))))))
(: gslt:automata:bind (-> Atom Atom %Undefined%))
(= (gslt:automata:bind $pattern $subject)
   (case $pattern
     (((FVar $name) (Some (LCons (Binding $name $subject) LNil)))
      ((Var $index) (if (== $pattern $subject) (Some LNil) None))
      ((PApp $head $children)
       (case $subject
         (((PApp $actual $arguments)
           (if (== $head $actual) (gslt:automata:bind-children $children $arguments) None))
          ($other None)))))))
(: gslt:automata:bind-children (-> Atom Atom %Undefined%))
(= (gslt:automata:bind-children $patterns $subjects)
   (case ($patterns $subjects)
     (((LNil LNil) (Some LNil))
      (((LCons $p $ps) (LCons $s $ss))
       (case ((gslt:automata:bind $p $s) (gslt:automata:bind-children $ps $ss))
         ((((Some $head) (Some $tail)) (gslt:automata:merge $head $tail))
          ($bad None))))
      ($bad None))))
(: gslt:automata:attempt-rows (-> Atom Atom Atom Atom Number %Undefined%))
(= (gslt:automata:attempt-rows $candidates $patterns $subject $path $next)
   (case $patterns ((LNil LNil) ((LCons $p $ps)
     (let $tail (gslt:automata:attempt-rows $candidates $ps $subject $path (+ $next 1))
       (if (gslt:automata:member (At $path $next) $candidates)
         (case (gslt:automata:bind $p $subject)
           (((Some $bindings) (LCons (Found $path $next $bindings) $tail)) (None $tail)))
         $tail))))))
(: gslt:automata:complete (-> Atom Atom Atom Atom %Undefined%))
(= (gslt:automata:complete $candidates $patterns $subject $path)
   (let $here (gslt:automata:attempt-rows $candidates $patterns $subject $path 0)
     (case $subject
       (((PApp $head $arguments)
         (let $below (gslt:automata:complete-children $candidates $patterns $arguments $path 0)
           (gslt:automata:append $here $below)))
        ($leaf $here)))))
(: gslt:automata:complete-children (-> Atom Atom Atom Atom Number %Undefined%))
(= (gslt:automata:complete-children $candidates $patterns $subjects $path $next)
   (case $subjects ((LNil LNil) ((LCons $s $ss)
     (let* (($child-path (gslt:automata:append $path (LCons $next LNil)))
            ($head (gslt:automata:complete $candidates $patterns $s $child-path))
            ($tail (gslt:automata:complete-children $candidates $patterns $ss $path (+ $next 1))))
       (gslt:automata:append $head $tail))))))

(: gslt:automata:bottom (-> Atom Atom %Undefined%))
(= (gslt:automata:bottom $patterns $subject)
   (let* (($shapes (gslt:automata:shapes $patterns))
          ($tree (gslt:automata:subject $subject))
          ($raw (gslt:automata:subpatterns-list $shapes))
          ($inventory (gslt:automata:unique $raw))
          ($state (gslt:automata:bottom-state $inventory $tree))
          ($locations (gslt:automata:bottom-locations $shapes $state LNil))
          ($matches (gslt:automata:complete $locations $patterns $subject LNil)))
     (case $state (((MState $root $children $reads $tests) (MatchRun $matches $reads $tests))))))
(: gslt:automata:top (-> Atom Atom %Undefined%))
(= (gslt:automata:top $patterns $subject)
   (let* (($shapes (gslt:automata:shapes $patterns))
          ($tree (gslt:automata:subject $subject))
          ($programs (gslt:automata:programs $shapes))
          ($observations (gslt:automata:observe $tree LNil))
          ($goals (gslt:automata:seed-all $observations $programs))
          ($run (gslt:automata:execute $observations $goals 0)))
     (case $run (((MFinished $remaining $dispatches)
       (let* (($locations (gslt:automata:completed $remaining))
              ($matches (gslt:automata:complete $locations $patterns $subject LNil))
              ($reads (gslt:automata:length $observations)))
         (MatchRun $matches $reads $dispatches)))))))

; The matching face of the existing canonical five-field LanguageDef wire.
; Premises, contracta, equations and contexts remain with the rule executor.
(: gslt:automata:language-patterns (-> Atom %Undefined%))
(= (gslt:automata:language-patterns
     (GSLTLanguageDefWireV1 $name $types $terms $equations $rewrites))
   (gslt:automata:rewrite-patterns $rewrites))
(: gslt:automata:rewrite-patterns (-> Atom %Undefined%))
(= (gslt:automata:rewrite-patterns $rewrites)
   (case $rewrites
     ((LNil LNil)
      ((LCons (RewriteRule $name $context $premises $left $right) $rest)
       (let $tail (gslt:automata:rewrite-patterns $rest) (LCons $left $tail))))))
(: gslt:automata:language-bottom (-> Atom Atom %Undefined%))
(= (gslt:automata:language-bottom $language $subject)
   (let $patterns (gslt:automata:language-patterns $language)
     (gslt:automata:bottom $patterns $subject)))
(: gslt:automata:language-top (-> Atom Atom %Undefined%))
(= (gslt:automata:language-top $language $subject)
   (let $patterns (gslt:automata:language-patterns $language)
     (gslt:automata:top $patterns $subject)))


; Canonical rule payload construction over the complete pattern wire.
; Binding lookup is shared with the matcher. Missing variables remain visible,
; and an inserted binding value is returned as data without further substitution.
(: gslt:rule:instantiate (-> Atom Atom %Undefined%))
(= (gslt:rule:instantiate $pattern $bindings)
   (case $pattern
     (((FVar $name)
       (case (gslt:automata:binding $name $bindings)
         ((None $pattern) ((Some $value) $value))))
      ((Var $index) $pattern)
      ((PApp $head $children)
       (let $arguments (gslt:rule:instantiate-children $children $bindings)
         (PApp $head $arguments)))
      ((PLam $binder $body)
       (let $value (gslt:rule:instantiate $body $bindings)
         (PLam $binder $value)))
      ((PMultiLam $arity $binders $body)
       (let $value (gslt:rule:instantiate $body $bindings)
         (PMultiLam $arity $binders $value)))
      ((PSubst $body $replacement)
       (let* (($value (gslt:rule:instantiate $body $bindings))
              ($replacement-value (gslt:rule:instantiate $replacement $bindings)))
         (gslt:rule:instantiate-bvar-at 0 $replacement-value $value)))
      ((PCollection $kind $elements $rest)
       (let $values (gslt:rule:instantiate-children $elements $bindings)
         (gslt:rule:instantiate-collection $kind $values $rest $bindings))))))
(: gslt:rule:instantiate-children (-> Atom Atom %Undefined%))
(= (gslt:rule:instantiate-children $patterns $bindings)
   (case $patterns
     ((LNil LNil)
      ((LCons $pattern $rest)
       (let* (($head (gslt:rule:instantiate $pattern $bindings))
              ($tail (gslt:rule:instantiate-children $rest $bindings)))
         (LCons $head $tail))))))
; Ordered RHS observations for the final bindings of a rule's premise runs.
(: gslt:rule:instantiate-results (-> Atom Atom %Undefined%))
(= (gslt:rule:instantiate-results $pattern $results)
   (case $results
     ((LNil LNil)
      ((LCons $bindings $rest)
       (let* (($value (gslt:rule:instantiate $pattern $bindings))
              ($tail (gslt:rule:instantiate-results $pattern $rest)))
         (LCons $value $tail))))))

; Root matching supplies no permission to rewrite a child position.
; Premise-free application is the composition of the shared binding matcher
; and RHS constructor; conditional rows use their premise continuations.
(: gslt:rule:apply-root (-> Atom Atom Atom %Undefined%))
(= (gslt:rule:apply-root $left $right $subject)
   (case (gslt:automata:bind $left $subject)
     ((None LNil)
      ((Some $bindings)
       (let $value (gslt:rule:instantiate $right $bindings)
         (LCons $value LNil))))))

; Relation arguments contribute bindings relative to the current seed.
; The complete tuple merges that extension with the original seed.
(: gslt:rule:relation-argument (-> Atom Atom Atom %Undefined%))
(= (gslt:rule:relation-argument $name $value $seed)
   (case (gslt:automata:binding $name $seed)
     ((None (Some (LCons (Binding $name $value) LNil)))
      ((Some $prior) (if (== $prior $value) (Some LNil) None)))))
(: gslt:rule:relation-arguments (-> Atom Atom Atom %Undefined%))
(= (gslt:rule:relation-arguments $names $values $seed)
   (case ($names $values)
     (((LNil LNil) (Some LNil))
      (((LCons $name $names-rest) (LCons $value $values-rest))
       (case (gslt:rule:relation-argument $name $value $seed)
         ((None None)
          ((Some $head)
           (case (gslt:automata:merge $seed $head)
             ((None None)
              ((Some $extended)
               (case (gslt:rule:relation-arguments $names-rest $values-rest $extended)
                 ((None None)
                  ((Some $tail) (gslt:automata:merge $head $tail)))))))))))
      ($bad None))))
(: gslt:rule:match-tuple (-> Atom Atom Atom %Undefined%))
(= (gslt:rule:match-tuple $names $values $seed)
   (case (gslt:rule:relation-arguments $names $values $seed)
     ((None None)
      ((Some $extended) (gslt:automata:merge $seed $extended)))))
(: gslt:rule:match-tuples (-> Atom Atom Atom %Undefined%))
(= (gslt:rule:match-tuples $names $tuples $seed)
   (case $tuples
     ((LNil LNil)
      ((LCons $values $rest)
       (let $tail (gslt:rule:match-tuples $names $rest $seed)
         (case (gslt:rule:match-tuple $names $values $seed)
           ((None $tail)
            ((Some $bindings) (LCons $bindings $tail)))))))))

; Ordered premise-free root observations from admitted canonical rule rows.
; A nonempty premise row does not enter this executor.
(: gslt:rule:root-reducts (-> Atom Atom %Undefined%))
(= (gslt:rule:root-reducts $rewrites $subject)
   (case $rewrites
     ((LNil LNil)
      ((LCons (RewriteRule $name $context LNil $left $right) $rest)
       (let* (($head (gslt:rule:apply-root $left $right $subject))
              ($tail (gslt:rule:root-reducts $rest $subject)))
         (gslt:automata:append $head $tail))))))

; The wire is a projection of an admitted language, not a raw-language validator.
; Empty equation rows are required in addition to the external generated-law
; admission used by the source-to-GSLT theorem.
(: gslt:rule:language-root-reducts (-> Atom Atom %Undefined%))
(= (gslt:rule:language-root-reducts $language $subject)
   (case $language
     (((GSLTLanguageDefWireV1 $name $types $terms LNil $rewrites)
       (gslt:rule:root-reducts $rewrites $subject)))))

; Literal immutable provider rows retain their authored order and multiplicity.
; Signature availability and typed row admission are separate from this view.
(: gslt:rule:provider-tuples (-> Atom Atom %Undefined%))
(= (gslt:rule:provider-tuples $relation $rows)
   (case $rows
     ((LNil LNil)
      ((LCons (ProviderRow $row-relation $values) $rest)
       (let $tail (gslt:rule:provider-tuples $relation $rest)
         (if (== $relation $row-relation)
             (LCons $values $tail) $tail))))))

; The canonical unscoped engine supplies two ordered equality witnesses.
; Their duplicate occurrences are retained when both arguments are equal.
(: gslt:rule:builtin-tuples (-> Atom Atom %Undefined%))
(= (gslt:rule:builtin-tuples $relation $arguments)
   (if (== $relation "eq")
       (case $arguments
         (((LCons $left (LCons $right LNil))
           (LCons (LCons $left (LCons $left LNil))
             (LCons (LCons $right (LCons $right LNil)) LNil)))
          ($bad LNil)))
       LNil))

(: gslt:rule:names-patterns (-> Atom %Undefined%))
(= (gslt:rule:names-patterns $names)
   (case $names
     ((LNil LNil)
      ((LCons $name $rest)
       (let $tail (gslt:rule:names-patterns $rest)
         (LCons (FVar $name) $tail))))))

; Query preparation substitutes names for the provider lookup, while tuple
; matching retains their original schemas and the seed's literal payloads.
(: gslt:rule:relation-query (-> Atom Atom Atom Atom %Undefined%))
(= (gslt:rule:relation-query $relation $names $rows $seed)
   (let* (($schemas (gslt:rule:names-patterns $names))
          ($arguments (gslt:rule:instantiate-children $schemas $seed))
          ($builtin (gslt:rule:builtin-tuples $relation $arguments))
          ($provided (gslt:rule:provider-tuples $relation $rows))
          ($tuples (gslt:automata:append $builtin $provided)))
     (gslt:rule:match-tuples $names $tuples $seed)))

; Only variable argument schemas enter the admitted first-order premise plan.
; Other canonical pattern forms have no successful name projection here.
(: gslt:rule:argument-names (-> Atom %Undefined%))
(= (gslt:rule:argument-names $arguments)
   (case $arguments
     ((LNil LNil)
      ((LCons (FVar $name) $rest)
       (let $tail (gslt:rule:argument-names $rest)
         (LCons $name $tail))))))

; The ordered fold branches on each query occurrence before continuing.
(: gslt:rule:premises (-> Atom Atom Atom %Undefined%))
(= (gslt:rule:premises $premises $rows $seed)
   (case $premises
     ((LNil (LCons $seed LNil))
      ((LCons (RelationQuery $relation $arguments) $rest)
       (let* (($names (gslt:rule:argument-names $arguments))
              ($choices (gslt:rule:relation-query $relation $names $rows $seed)))
         (gslt:rule:premise-results $rest $rows $choices))))))

(: gslt:rule:premise-results (-> Atom Atom Atom %Undefined%))
(= (gslt:rule:premise-results $premises $rows $results)
   (case $results
     ((LNil LNil)
      ((LCons $seed $rest)
       (let* (($head (gslt:rule:premises $premises $rows $seed))
              ($tail (gslt:rule:premise-results $premises $rows $rest)))
         (gslt:automata:append $head $tail))))))

(: gslt:rule:apply-conditional (-> Atom Atom Atom Atom Atom %Undefined%))
(= (gslt:rule:apply-conditional $left $right $premises $rows $subject)
   (case (gslt:automata:bind $left $subject)
     ((None LNil)
      ((Some $seed)
       (let $results (gslt:rule:premises $premises $rows $seed)
         (gslt:rule:instantiate-results $right $results))))))

(: gslt:rule:conditional-root-reducts (-> Atom Atom Atom %Undefined%))
(= (gslt:rule:conditional-root-reducts $rewrites $rows $subject)
   (case $rewrites
     ((LNil LNil)
      ((LCons (RewriteRule $name $context $premises $left $right) $rest)
       (let* (($head (gslt:rule:apply-conditional $left $right $premises $rows $subject))
              ($tail (gslt:rule:conditional-root-reducts $rest $rows $subject)))
         (gslt:automata:append $head $tail))))))

; Generated equations also remain subject to the external admission theorem.
(: gslt:rule:language-conditional-root-reducts (-> Atom Atom Atom %Undefined%))
(= (gslt:rule:language-conditional-root-reducts $language $rows $subject)
   (case $language
     (((GSLTLanguageDefWireV1 $name $types $terms LNil $rewrites)
      (gslt:rule:conditional-root-reducts $rewrites $rows $subject)))))

; Occurrence lookup retains the physical authored row. Matchers supply the
; index; invalid indices and matches below the root grant no step.
(: gslt:rule:row-at (-> Atom Atom %Undefined%))
(= (gslt:rule:row-at $index $rewrites)
   (case $rewrites
     ((LNil None)
      ((LCons $row $rest)
       (if (== $index 0) (Some $row)
         (let $previous (- $index 1) (gslt:rule:row-at $previous $rest)))))))

(: gslt:rule:apply-root-match (-> Atom Atom Atom %Undefined%))
(= (gslt:rule:apply-root-match $rewrites $rows $matched)
   (case $matched
     (((Found LNil $index $seed)
       (let $selected (gslt:rule:row-at $index $rewrites)
         (case $selected
           ((None LNil)
            ((Some (RewriteRule $name $context $premises $left $right))
             (let $choices (gslt:rule:premises $premises $rows $seed)
               (gslt:rule:instantiate-results $right $choices)))))))
      ((Found (LCons $child $path) $index $seed) LNil))))

(: gslt:rule:matched-root-reducts (-> Atom Atom Atom %Undefined%))
(= (gslt:rule:matched-root-reducts $rewrites $rows $matches)
   (case $matches
     ((LNil LNil)
      ((LCons $matched $rest)
       (let* (($head (gslt:rule:apply-root-match $rewrites $rows $matched))
              ($tail (gslt:rule:matched-root-reducts $rewrites $rows $rest)))
         (gslt:automata:append $head $tail))))))

(: gslt:rule:language-bottom-reducts (-> Atom Atom Atom %Undefined%))
(= (gslt:rule:language-bottom-reducts $language $rows $subject)
   (case $language
     (((GSLTLanguageDefWireV1 $name $types $terms LNil $rewrites)
       (let $matched (gslt:automata:language-bottom $language $subject)
         (case $matched
           (((MatchRun $matches $reads $tests)
             (gslt:rule:matched-root-reducts $rewrites $rows $matches)))))))))

(: gslt:rule:language-top-reducts (-> Atom Atom Atom %Undefined%))
(= (gslt:rule:language-top-reducts $language $rows $subject)
   (case $language
     (((GSLTLanguageDefWireV1 $name $types $terms LNil $rewrites)
       (let $matched (gslt:automata:language-top $language $subject)
         (case $matched
           (((MatchRun $matches $reads $tests)
             (gslt:rule:matched-root-reducts $rewrites $rows $matches)))))))))

; The ordinal selects one physical frontier occurrence. Stopping because
; receipts run out does not assert that the residual is a normal form.
(: gslt:rule:drive (-> Atom Atom Atom Atom Atom %Undefined%))
(= (gslt:rule:drive $language $rows $subject $selections $budget)
   (case $selections
     ((LNil (RuleTraceStopped $subject))
      ((LCons $index $rest)
       (if (== $budget 0)
         (RuleTraceFuelExhausted $subject $selections)
         (let $frontier (gslt:rule:language-conditional-root-reducts $language $rows $subject)
           (case (gslt:rule:row-at $index $frontier)
             ((None (RuleTraceRefused $subject $selections $frontier))
              ((Some $next)
               (let* (($remaining (- $budget 1))
                      ($tail (gslt:rule:drive $language $rows $next $rest $remaining)))
                 (RuleTraceStep $subject $index $frontier $tail)))))))))))

; A recursive premise matches each candidate relative to the original seed,
; then merges that extension. Candidate order and duplicate witnesses remain.
(: gslt:rule:recursive-results (-> Atom Atom Atom %Undefined%))
(= (gslt:rule:recursive-results $target $candidates $seed)
   (case $candidates
     ((LNil LNil)
      ((LCons $candidate $rest)
       (let $tail (gslt:rule:recursive-results $target $rest $seed)
         (case (gslt:automata:bind $target $candidate)
           ((None $tail)
            ((Some $relative)
             (case (gslt:automata:merge $seed $relative)
               ((None $tail)
                ((Some $extended) (LCons $extended $tail))))))))))))

; Depth bounds recursive premise evidence, independently of trace selections.
(: gslt:rule:premises-at (-> Atom Atom Atom Atom Atom Atom %Undefined%))
(= (gslt:rule:premises-at $strategy $language $rows $depth $premises $seed)
   (case $premises
     ((LNil (LCons $seed LNil))
      ((LCons (Freshness $name $term) $rest)
       (let $choices (gslt:premise:freshness $name $term $seed)
         (gslt:rule:premise-results-at $strategy $language $rows $depth $rest $choices)))
      ((LCons (RelationQuery $relation $arguments) $rest)
       (let* (($names (gslt:rule:argument-names $arguments))
              ($choices (gslt:rule:relation-query $relation $names $rows $seed)))
         (gslt:rule:premise-results-at $strategy $language $rows $depth $rest $choices)))
      ((LCons (Congruence $source $target) $rest)
       (let* (($instance (gslt:rule:instantiate $source $seed))
              ($candidates (gslt:rule:language-contextual-reducts $strategy $language $rows $depth $instance))
              ($choices (gslt:rule:recursive-results $target $candidates $seed)))
         (gslt:rule:premise-results-at $strategy $language $rows $depth $rest $choices))))))

(: gslt:rule:premise-results-at (-> Atom Atom Atom Atom Atom Atom %Undefined%))
(= (gslt:rule:premise-results-at $strategy $language $rows $depth $premises $results)
   (case $results
     ((LNil LNil)
      ((LCons $seed $rest)
       (let* (($head (gslt:rule:premises-at $strategy $language $rows $depth $premises $seed))
              ($tail (gslt:rule:premise-results-at $strategy $language $rows $depth $premises $rest)))
         (gslt:automata:append $head $tail))))))

(: gslt:rule:apply-root-match-at (-> Atom Atom Atom Atom Atom Atom %Undefined%))
(= (gslt:rule:apply-root-match-at $strategy $language $rewrites $rows $depth $matched)
   (case $matched
     (((Found LNil $index $seed)
       (let $selected (gslt:rule:row-at $index $rewrites)
         (case $selected
           ((None LNil)
            ((Some (RewriteRule $name $context $premises $left $right))
             (let $choices (gslt:rule:premises-at $strategy $language $rows $depth $premises $seed)
               (gslt:rule:instantiate-results $right $choices)))))))
      ((Found (LCons $child $path) $index $seed) LNil))))

(: gslt:rule:matched-root-reducts-at (-> Atom Atom Atom Atom Atom Atom %Undefined%))
(= (gslt:rule:matched-root-reducts-at $strategy $language $rewrites $rows $depth $matches)
   (case $matches
     ((LNil LNil)
      ((LCons $matched $rest)
       (let* (($head (gslt:rule:apply-root-match-at $strategy $language $rewrites $rows $depth $matched))
              ($tail (gslt:rule:matched-root-reducts-at $strategy $language $rewrites $rows $depth $rest)))
         (gslt:automata:append $head $tail))))))

(: gslt:rule:language-matches (-> Atom Atom Atom %Undefined%))
(= (gslt:rule:language-matches $strategy $language $subject)
   (case $strategy
     ((MatchBottomUp (gslt:automata:language-bottom $language $subject))
      (MatchTopDown (gslt:automata:language-top $language $subject)))))

; Contextual rewriting is authored as a rule with a recursive premise.
; Inspecting a child never grants permission to replace that child by itself.
(: gslt:rule:language-contextual-reducts (-> Atom Atom Atom Atom Atom %Undefined%))
(= (gslt:rule:language-contextual-reducts $strategy $language $rows $depth $subject)
   (if (== $depth 0) LNil
     (case $language
       (((GSLTLanguageDefWireV1 $name $types $terms LNil $rewrites)
         (let* (($previous (- $depth 1))
                ($matched (gslt:rule:language-matches $strategy $language $subject)))
           (case $matched
             (((MatchRun $matches $reads $tests)
               (gslt:rule:matched-root-reducts-at $strategy $language $rewrites $rows $previous $matches))))))))))

(: gslt:rule:language-contextual-bottom-reducts (-> Atom Atom Atom Atom %Undefined%))
(= (gslt:rule:language-contextual-bottom-reducts $language $rows $depth $subject)
   (gslt:rule:language-contextual-reducts MatchBottomUp $language $rows $depth $subject))

(: gslt:rule:language-contextual-top-reducts (-> Atom Atom Atom Atom %Undefined%))
(= (gslt:rule:language-contextual-top-reducts $language $rows $depth $subject)
   (gslt:rule:language-contextual-reducts MatchTopDown $language $rows $depth $subject))

; Canonical bound-variable lifting preserves display and rest metadata.
(: gslt:rule:lift-bvars (-> Atom Atom Atom %Undefined%))
(= (gslt:rule:lift-bvars $cutoff $shift $pattern)
   (case $pattern
     (((Var $index)
       (if (>= $index $cutoff)
           (let $next (+ $index $shift) (Var $next)) $pattern))
      ((FVar $name) $pattern)
      ((PApp $head $children)
       (let $arguments (gslt:rule:lift-bvars-list $cutoff $shift $children)
         (PApp $head $arguments)))
      ((PLam $binder $body)
       (let* (($next (+ $cutoff 1))
              ($value (gslt:rule:lift-bvars $next $shift $body)))
         (PLam $binder $value)))
      ((PMultiLam $arity $binders $body)
       (let* (($next (+ $cutoff $arity))
              ($value (gslt:rule:lift-bvars $next $shift $body)))
         (PMultiLam $arity $binders $value)))
      ((PSubst $body $replacement)
       (let* (($next (+ $cutoff 1))
              ($value (gslt:rule:lift-bvars $next $shift $body))
              ($replacement-value (gslt:rule:lift-bvars $cutoff $shift $replacement)))
         (PSubst $value $replacement-value)))
      ((PCollection $kind $elements $rest)
       (let $values (gslt:rule:lift-bvars-list $cutoff $shift $elements)
         (PCollection $kind $values $rest))))))
(: gslt:rule:lift-bvars-list (-> Atom Atom Atom %Undefined%))
(= (gslt:rule:lift-bvars-list $cutoff $shift $patterns)
   (case $patterns
     ((LNil LNil)
      ((LCons $pattern $rest)
       (let* (($head (gslt:rule:lift-bvars $cutoff $shift $pattern))
              ($tail (gslt:rule:lift-bvars-list $cutoff $shift $rest)))
         (LCons $head $tail))))))

; Elimination removes one surrounding binder and lifts the replacement under
; intervening binders. Nested explicit substitutions retain their own level.
(: gslt:rule:instantiate-bvar-at (-> Atom Atom Atom %Undefined%))
(= (gslt:rule:instantiate-bvar-at $depth $replacement $pattern)
   (case $pattern
     (((Var $index)
       (if (< $index $depth) $pattern
           (if (== $index $depth)
               (gslt:rule:lift-bvars 0 $depth $replacement)
               (let $next (- $index 1) (Var $next)))))
      ((FVar $name) $pattern)
      ((PApp $head $children)
       (let $arguments (gslt:rule:instantiate-bvar-list-at $depth $replacement $children)
         (PApp $head $arguments)))
      ((PLam $binder $body)
       (let* (($next (+ $depth 1))
              ($value (gslt:rule:instantiate-bvar-at $next $replacement $body)))
         (PLam $binder $value)))
      ((PMultiLam $arity $binders $body)
       (let* (($next (+ $depth $arity))
              ($value (gslt:rule:instantiate-bvar-at $next $replacement $body)))
         (PMultiLam $arity $binders $value)))
      ((PSubst $body $nested-replacement)
       (let* (($next (+ $depth 1))
              ($value (gslt:rule:instantiate-bvar-at $next $replacement $body))
              ($replacement-value (gslt:rule:instantiate-bvar-at $depth $replacement $nested-replacement)))
         (PSubst $value $replacement-value)))
      ((PCollection $kind $elements $rest)
       (let $values (gslt:rule:instantiate-bvar-list-at $depth $replacement $elements)
         (PCollection $kind $values $rest))))))
(: gslt:rule:instantiate-bvar-list-at (-> Atom Atom Atom %Undefined%))
(= (gslt:rule:instantiate-bvar-list-at $depth $replacement $patterns)
   (case $patterns
     ((LNil LNil)
      ((LCons $pattern $rest)
       (let* (($head (gslt:rule:instantiate-bvar-at $depth $replacement $pattern))
              ($tail (gslt:rule:instantiate-bvar-list-at $depth $replacement $rest)))
         (LCons $head $tail))))))

; A resolved same-kind closed collection contributes its captured elements
; unchanged. All other rest bindings leave the original rest visible.
(: gslt:rule:instantiate-collection (-> Atom Atom Atom Atom %Undefined%))
(= (gslt:rule:instantiate-collection $kind $elements $rest $bindings)
   (case $rest
     ((RNone (PCollection $kind $elements RNone))
      ((RSome $name)
       (case (gslt:automata:binding $name $bindings)
         (((Some (PCollection $bound-kind $bound-elements RNone))
           (if (== $kind $bound-kind)
               (let $all (gslt:automata:append $elements $bound-elements)
                 (PCollection $kind $all RNone))
               (PCollection $kind $elements $rest)))
          ($unresolved (PCollection $kind $elements $rest))))))))

; Scoped capture operations on the existing Pattern and ContextualValue wire.
; Simultaneous substitution preserves explicit PSubst nodes. Its finite
; descriptors denote the canonical occurrence and recovery assignments.
(: gslt:rule:scope-well-scoped (-> Atom Atom %Undefined%))
(= (gslt:rule:scope-well-scoped $depth $pattern)
   (case $pattern
     (((Var $index) (< $index $depth))
      ((FVar $name) True)
      ((PApp $head $children)
       (gslt:rule:scope-well-scoped-list $depth $children))
      ((PLam $binder $body)
       (let $next (+ $depth 1) (gslt:rule:scope-well-scoped $next $body)))
      ((PMultiLam $arity $binders $body)
       (let $next (+ $depth $arity) (gslt:rule:scope-well-scoped $next $body)))
      ((PSubst $body $replacement)
       (let $next (+ $depth 1)
         (if (gslt:rule:scope-well-scoped $next $body)
           (gslt:rule:scope-well-scoped $depth $replacement) False)))
      ((PCollection $kind $elements $rest)
       (gslt:rule:scope-well-scoped-list $depth $elements))
      ($invalid False))))
(: gslt:rule:scope-well-scoped-list (-> Atom Atom %Undefined%))
(= (gslt:rule:scope-well-scoped-list $depth $patterns)
   (case $patterns
     ((LNil True)
      ((LCons $pattern $rest)
       (if (gslt:rule:scope-well-scoped $depth $pattern)
         (gslt:rule:scope-well-scoped-list $depth $rest) False))
      ($invalid False))))
(: gslt:rule:scope-index (-> Atom Atom %Undefined%))
(= (gslt:rule:scope-index $index $indices)
   (case $indices
     ((LNil None)
      ((LCons $first $rest)
       (if (== $index $first) (Some 0)
         (case (gslt:rule:scope-index $index $rest)
           ((None None)
            ((Some $position)
             (let $next (+ $position 1) (Some $next)))))))
      ($invalid None))))
(: gslt:rule:scope-variable-spine (-> Atom Atom %Undefined%))
(= (gslt:rule:scope-variable-spine $depth $arguments)
   (case $arguments
     ((LNil (Some LNil))
      ((LCons $argument $rest)
       (case $argument
         (((Var $index)
           (if (< $index $depth)
             (case (gslt:rule:scope-variable-spine $depth $rest)
               ((None None)
                ((Some $indices)
                 (if (gslt:automata:member $index $indices) None
                   (let $all (LCons $index $indices) (Some $all)))))) None))
          ($nonvariable None))))
      ($invalid None))))
(: gslt:rule:scope-assignment (-> Atom Atom %Undefined%))
(= (gslt:rule:scope-assignment $assignment $index)
   (case $assignment
     (((OccurrenceAssignment $dependencies $depth $arguments)
       (if (< $index $dependencies)
         (case (gslt:rule:row-at $index $arguments)
           ((None (Var 0)) ((Some $value) $value)))
         (let* (($offset (- $index $dependencies))
                ($shifted (+ $depth $offset)))
           (Var $shifted))))
      ((RecoveryAssignment $depth $dependencies $ambient $indices)
       (if (< $index $depth)
         (case (gslt:rule:scope-index $index $indices)
           ((None (let $outside (+ $dependencies $ambient) (Var $outside)))
            ((Some $position) (Var $position))))
         (let* (($offset (- $index $depth))
                ($shifted (+ $dependencies $offset)))
           (Var $shifted))))
      ($invalid None))))
(: gslt:rule:scope-substitute (-> Atom Atom Atom %Undefined%))
(= (gslt:rule:scope-substitute $assignment $prefix $pattern)
   (case $pattern
     (((Var $index)
       (if (< $index $prefix) $pattern
         (let* (($original (- $index $prefix))
                ($image (gslt:rule:scope-assignment $assignment $original)))
           (gslt:rule:lift-bvars 0 $prefix $image))))
      ((FVar $name) $pattern)
      ((PApp $head $children)
       (let $values (gslt:rule:scope-substitute-list $assignment $prefix $children)
         (PApp $head $values)))
      ((PLam $binder $body)
       (let* (($next (+ $prefix 1))
              ($value (gslt:rule:scope-substitute $assignment $next $body)))
         (PLam $binder $value)))
      ((PMultiLam $arity $binders $body)
       (let* (($next (+ $prefix $arity))
              ($value (gslt:rule:scope-substitute $assignment $next $body)))
         (PMultiLam $arity $binders $value)))
      ((PSubst $body $replacement)
       (let* (($next (+ $prefix 1))
              ($value (gslt:rule:scope-substitute $assignment $next $body))
              ($replacement-value (gslt:rule:scope-substitute $assignment $prefix $replacement)))
         (PSubst $value $replacement-value)))
      ((PCollection $kind $elements $rest)
       (let $values (gslt:rule:scope-substitute-list $assignment $prefix $elements)
         (PCollection $kind $values $rest)))
      ($invalid None))))
(: gslt:rule:scope-substitute-list (-> Atom Atom Atom %Undefined%))
(= (gslt:rule:scope-substitute-list $assignment $prefix $patterns)
   (case $patterns
     ((LNil LNil)
      ((LCons $pattern $rest)
       (let* (($head (gslt:rule:scope-substitute $assignment $prefix $pattern))
              ($tail (gslt:rule:scope-substitute-list $assignment $prefix $rest)))
         (LCons $head $tail)))
      ($invalid None))))
(: gslt:rule:scope-instantiate-value (-> Atom Atom Atom Atom %Undefined%))
(= (gslt:rule:scope-instantiate-value $value $ambient $depth $arguments)
   (case $value
     (((ContextualValue $dependencies $stored-ambient $body)
       (if (== $stored-ambient $ambient)
         (let* (($arity (gslt:automata:length $dependencies))
                ($supplied (gslt:automata:length $arguments)))
           (if (== $supplied $arity)
             (let* (($source-depth (+ $arity $ambient))
                    ($target-depth (+ $depth $ambient)))
               (if (gslt:rule:scope-well-scoped $source-depth $body)
                 (if (gslt:rule:scope-well-scoped-list $target-depth $arguments)
                   (let* (($assignment (OccurrenceAssignment $arity $depth $arguments))
                          ($result (gslt:rule:scope-substitute $assignment 0 $body)))
                     (if (gslt:rule:scope-well-scoped $target-depth $result)
                       (Some $result) None)) None) None)) None)) None))
      ($invalid None))))
(: gslt:rule:scope-recover-value (-> Atom Atom Atom Atom Atom %Undefined%))
(= (gslt:rule:scope-recover-value $dependencies $ambient $depth $arguments $target)
   (let $target-depth (+ $depth $ambient)
     (if (gslt:rule:scope-well-scoped $target-depth $target)
       (case (gslt:rule:scope-variable-spine $depth $arguments)
         ((None None)
          ((Some $indices)
           (let* (($arity (gslt:automata:length $dependencies))
                  ($supplied (gslt:automata:length $indices)))
             (if (== $supplied $arity)
               (let* (($assignment (RecoveryAssignment $depth $arity $ambient $indices))
                      ($body (gslt:rule:scope-substitute $assignment 0 $target))
                      ($value (ContextualValue $dependencies $ambient $body))
                      ($forward (gslt:rule:scope-instantiate-value $value $ambient $depth $arguments)))
                 (if (== $forward (Some $target)) (Some $value) None)) None))))) None)))
(: gslt:rule:scope-assign (-> Atom Atom Atom %Undefined%))
(= (gslt:rule:scope-assign $assignment $name $value)
   (case (gslt:automata:binding $name $assignment)
     ((None
       (let* (($entry (Binding $name $value))
              ($extended (LCons $entry $assignment))) (Some $extended)))
      ((Some $prior) (if (== $prior $value) (Some $assignment) None)))))

; Canonical authored binding metadata and occurrence capture.
(: gslt:rule:scope-metadata-dependency-rows (-> Atom Atom %Undefined%))
(= (gslt:rule:scope-metadata-dependency-rows $rows $name)
   (case $rows
     ((LNil LNil)
      ((LCons (RuleDependency $declared $sorts) $rest)
       (let $tail (gslt:rule:scope-metadata-dependency-rows $rest $name)
         (if (== $name $declared)
           (LCons (RuleDependency $declared $sorts) $tail) $tail)))
      ($invalid LNil))))
(: gslt:rule:scope-metadata-dependencies (-> Atom Atom %Undefined%))
(= (gslt:rule:scope-metadata-dependencies $spec $name)
   (case $spec
     (((RuleBindingSpec $dependencies $occurrences)
       (case (gslt:rule:scope-metadata-dependency-rows $dependencies $name)
         (((LCons (RuleDependency $declared $sorts) LNil) (Some $sorts))
          ($other None))))
      ($invalid None))))
(: gslt:rule:scope-metadata-occurrence-rows (-> Atom Atom Atom Atom %Undefined%))
(= (gslt:rule:scope-metadata-occurrence-rows $rows $name $site $path)
   (case $rows
     ((LNil LNil)
      ((LCons (RuleOccurrence $declared $actual-site $actual-path $arguments) $rest)
       (let $tail (gslt:rule:scope-metadata-occurrence-rows $rest $name $site $path)
         (if (== $name $declared)
           (if (== $site $actual-site)
             (if (== $path $actual-path)
               (LCons (RuleOccurrence $declared $actual-site $actual-path $arguments) $tail)
               $tail) $tail) $tail)))
      ($invalid LNil))))
(: gslt:rule:scope-metadata-quantified-body (-> Atom Atom %Undefined%))
(= (gslt:rule:scope-metadata-quantified-body $count $premise)
   (if (== $count 0) (Some $premise)
     (case $premise
       (((ForAll $collection $parameter $body)
         (let $previous (- $count 1)
           (gslt:rule:scope-metadata-quantified-body $previous $body)))
        ($other None)))))
(: gslt:rule:scope-metadata-site-premise (-> Atom Atom Atom %Undefined%))
(= (gslt:rule:scope-metadata-site-premise $rule $index $quantifiers)
   (case $rule
     (((ScopedRewriteRuleV1 $rule-name $context $premises $left $right $bindings)
       (case (gslt:rule:row-at $index $premises)
         (((Some $premise) (gslt:rule:scope-metadata-quantified-body $quantifiers $premise))
          ($other None))))
      ($invalid None))))
(: gslt:rule:scope-metadata-premise-pattern (-> Atom Atom %Undefined%))
(= (gslt:rule:scope-metadata-premise-pattern $premise $argument)
   (case $premise
     (((Freshness $name $pattern)
       (if (== $argument 0) (Some $pattern) None))
      ((Congruence $source $target)
       (if (== $argument 0) (Some $source)
         (if (== $argument 1) (Some $target) None)))
      ((ScopedStep $binders $sort $source $target)
       (if (== $argument 0) (Some $source)
         (if (== $argument 1) (Some $target) None)))
      ((RelationQuery $relation $arguments) (gslt:rule:row-at $argument $arguments))
      ($other None))))
(: gslt:rule:scope-metadata-premise-depth (-> Atom Atom %Undefined%))
(= (gslt:rule:scope-metadata-premise-depth $premise $argument)
   (case $premise
     (((Freshness $name $pattern) (if (== $argument 0) (Some 0) None))
      ((Congruence $source $target) (if (< $argument 2) (Some 0) None))
      ((ScopedStep $binders $sort $source $target)
       (if (< $argument 2) (let $depth (gslt:automata:length $binders) (Some $depth)) None))
      ((RelationQuery $relation $arguments)
       (let $length (gslt:automata:length $arguments)
         (if (< $argument $length) (Some 0) None)))
      ($other None))))
(: gslt:rule:scope-metadata-site-pattern (-> Atom Atom %Undefined%))
(= (gslt:rule:scope-metadata-site-pattern $rule $site)
   (case $rule
     (((ScopedRewriteRuleV1 $rule-name $context $premises $left $right $bindings)
       (case $site
         ((RuleLeft (Some $left))
          (RuleRight (Some $right))
          ((RulePremise $index $quantifiers $argument)
           (case (gslt:rule:scope-metadata-site-premise $rule $index $quantifiers)
             (((Some $premise) (gslt:rule:scope-metadata-premise-pattern $premise $argument))
              ($other None))))
          ($unknown None))))
      ($invalid None))))
(: gslt:rule:scope-metadata-site-depth (-> Atom Atom %Undefined%))
(= (gslt:rule:scope-metadata-site-depth $rule $site)
   (case $site
     ((RuleLeft (Some 0))
      (RuleRight (Some 0))
      ((RulePremise $index $quantifiers $argument)
       (case (gslt:rule:scope-metadata-site-premise $rule $index $quantifiers)
         (((Some $premise) (gslt:rule:scope-metadata-premise-depth $premise $argument))
          ($other None))))
      ($unknown None))))
(: gslt:rule:scope-metadata-occurrence-name (-> Atom Atom %Undefined%))
(= (gslt:rule:scope-metadata-occurrence-name $pattern $path)
   (case $path
     ((LNil (case $pattern (((FVar $name) (Some $name)) ($other None))))
      ((LCons $index $rest)
       (case $pattern
         (((PApp $head $arguments)
           (case (gslt:rule:row-at $index $arguments)
             (((Some $child) (gslt:rule:scope-metadata-occurrence-name $child $rest)) ($missing None))))
          ((PLam $binder $body)
           (if (== $index 0) (gslt:rule:scope-metadata-occurrence-name $body $rest) None))
          ((PMultiLam $arity $binders $body)
           (if (== $index 0) (gslt:rule:scope-metadata-occurrence-name $body $rest) None))
          ((PSubst $body $replacement)
           (if (== $index 0) (gslt:rule:scope-metadata-occurrence-name $body $rest)
             (if (== $index 1) (gslt:rule:scope-metadata-occurrence-name $replacement $rest) None)))
          ((PCollection $kind $elements $tail)
           (let $length (gslt:automata:length $elements)
             (if (< $index $length)
               (case (gslt:rule:row-at $index $elements)
                 (((Some $child) (gslt:rule:scope-metadata-occurrence-name $child $rest)) ($missing None)))
               (if (== $index $length)
                 (case $rest
                   ((LNil (case $tail (((RSome $name) (Some $name)) ($missing None))))
                    ($remaining None))) None))))
          ($other None))))
      ($invalid None))))
(: gslt:rule:scope-metadata-occurrence-depth (-> Atom Atom Atom %Undefined%))
(= (gslt:rule:scope-metadata-occurrence-depth $pattern $path $depth)
   (case $path
     ((LNil (case $pattern (((FVar $name) (Some $depth)) ($other None))))
      ((LCons $index $rest)
       (case $pattern
         (((PApp $head $arguments)
           (case (gslt:rule:row-at $index $arguments)
             (((Some $child) (gslt:rule:scope-metadata-occurrence-depth $child $rest $depth)) ($missing None))))
          ((PLam $binder $body)
           (if (== $index 0)
             (let $next (+ $depth 1) (gslt:rule:scope-metadata-occurrence-depth $body $rest $next)) None))
          ((PMultiLam $arity $binders $body)
           (if (== $index 0)
             (let $next (+ $depth $arity) (gslt:rule:scope-metadata-occurrence-depth $body $rest $next)) None))
          ((PSubst $body $replacement)
           (if (== $index 0)
             (let $next (+ $depth 1) (gslt:rule:scope-metadata-occurrence-depth $body $rest $next))
             (if (== $index 1) (gslt:rule:scope-metadata-occurrence-depth $replacement $rest $depth) None)))
          ((PCollection $kind $elements $tail)
           (let $length (gslt:automata:length $elements)
             (if (< $index $length)
               (case (gslt:rule:row-at $index $elements)
                 (((Some $child) (gslt:rule:scope-metadata-occurrence-depth $child $rest $depth)) ($missing None)))
               (if (== $index $length)
                 (case $rest
                   ((LNil (case $tail (((RSome $name) (Some $depth)) ($missing None))))
                    ($remaining None))) None))))
          ($other None))))
      ($invalid None))))
(: gslt:rule:scope-metadata-occurrence-depth-at-site (-> Atom Atom Atom %Undefined%))
(= (gslt:rule:scope-metadata-occurrence-depth-at-site $rule $site $path)
   (case (gslt:rule:scope-metadata-site-pattern $rule $site)
     (((Some $pattern)
       (case (gslt:rule:scope-metadata-site-depth $rule $site)
         (((Some $depth) (gslt:rule:scope-metadata-occurrence-depth $pattern $path $depth))
          ($no-depth None))))
      ($no-pattern None))))
(: gslt:rule:scope-metadata-occurrence-declared (-> Atom Atom %Undefined%))
(= (gslt:rule:scope-metadata-occurrence-declared $rule $occurrence)
   (case $occurrence
     (((RuleOccurrence $name $site $path $arguments)
       (case (gslt:rule:scope-metadata-site-pattern $rule $site)
         (((Some $pattern)
           (let $observed (gslt:rule:scope-metadata-occurrence-name $pattern $path)
             (== $observed (Some $name))))
          ($other False))))
      ($invalid False))))
(: gslt:rule:scope-metadata-arguments (-> Atom Atom Atom Atom Atom %Undefined%))
(= (gslt:rule:scope-metadata-arguments $rule $spec $name $site $path)
   (case (gslt:rule:scope-metadata-dependencies $spec $name)
     (((Some $dependencies)
       (if (gslt:rule:scope-metadata-occurrence-declared $rule (RuleOccurrence $name $site $path LNil))
         (case $spec
           (((RuleBindingSpec $dependency-rows $occurrences)
             (case (gslt:rule:scope-metadata-occurrence-rows $occurrences $name $site $path)
               ((LNil (if (== $dependencies LNil) (Some LNil) None))
                ((LCons (RuleOccurrence $actual-name $actual-site $actual-path $arguments) LNil)
                 (if (gslt:rule:scope-metadata-occurrence-declared $rule
                       (RuleOccurrence $actual-name $actual-site $actual-path $arguments))
                   (let* (($arity (gslt:automata:length $dependencies))
                          ($supplied (gslt:automata:length $arguments)))
                     (if (== $supplied $arity) (Some $arguments) None)) None))
                ($ambiguous None))))
            ($invalid None))) None))
      ($unknown None))))
(: gslt:rule:scope-metadata-capture (-> Atom Atom Atom Atom Atom Atom Atom %Undefined%))
(= (gslt:rule:scope-metadata-capture $rule $ambient $site $path $assignment $name $target)
   (case $rule
     (((ScopedRewriteRuleV1 $rule-name $context $premises $left $right $bindings)
       (case $bindings
         (((RuleBindingSome $spec)
           (case (gslt:rule:scope-metadata-occurrence-depth-at-site $rule $site $path)
             (((Some $depth)
               (case (gslt:rule:scope-metadata-dependencies $spec $name)
                 (((Some $dependencies)
                   (case (gslt:rule:scope-metadata-arguments $rule $spec $name $site $path)
                     (((Some $arguments)
                       (case (gslt:rule:scope-recover-value $dependencies $ambient $depth $arguments $target)
                         (((Some $value) (gslt:rule:scope-assign $assignment $name $value))
                          ($failed None))))
                      ($no-arguments None))))
                  ($no-dependencies None))))
              ($no-depth None))))
          ($no-spec None))))
      ($invalid None))))
(: gslt:rule:scope-metadata-capture-rest (-> Atom Atom Atom Atom Atom Atom Atom Atom %Undefined%))
(= (gslt:rule:scope-metadata-capture-rest $rule $ambient $site $path $assignment $name $kind $elements)
   (gslt:rule:scope-metadata-capture $rule $ambient $site $path $assignment $name
     (PCollection $kind $elements RNone)))

; Ordered scoped matching over the retained Pattern wire.
; Every capture reads its actual metadata site and depth from the original rule.
(: gslt:rule:scope-match (-> Atom Atom Atom Atom Atom Atom Atom %Undefined%))
(= (gslt:rule:scope-match $rule $ambient $site $path $assignment $schema $target)
   (case $schema
     (((FVar $name)
       (case (gslt:rule:scope-metadata-capture $rule $ambient $site $path $assignment $name $target)
         ((None LNil) ((Some $found) (LCons $found LNil)))))
      ((Var $index) (if (== $schema $target) (LCons $assignment LNil) LNil))
      ((PApp $label $patterns)
       (case $target
         (((PApp $actual $targets)
           (if (== $label $actual)
             (gslt:rule:scope-match-arguments $rule $ambient $site $path $assignment 0 $patterns $targets)
             LNil))
          ($other LNil))))
      ((PLam $display $body)
       (case $target
         (((PLam $actual-display $actual-body)
           (let $nested (gslt:automata:append $path (LCons 0 LNil))
             (gslt:rule:scope-match $rule $ambient $site $nested $assignment $body $actual-body)))
          ($other LNil))))
      ((PMultiLam $arity $display $body)
       (case $target
         (((PMultiLam $actual-arity $actual-display $actual-body)
           (if (== $arity $actual-arity)
             (let $nested (gslt:automata:append $path (LCons 0 LNil))
               (gslt:rule:scope-match $rule $ambient $site $nested $assignment $body $actual-body))
             LNil))
          ($other LNil))))
      ((PSubst $body $replacement)
       (case $target
         (((PSubst $actual-body $actual-replacement)
           (let $nested (gslt:automata:append $path (LCons 0 LNil))
             (let $heads (gslt:rule:scope-match $rule $ambient $site $nested $assignment $body $actual-body)
               (gslt:rule:scope-match-arguments-results $rule $ambient $site $path $heads 1
                 (LCons $replacement LNil) (LCons $actual-replacement LNil)))))
          ($other LNil))))
      ((PCollection "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.vec" $patterns $rest)
       (case $target
         (((PCollection "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.vec" $targets RNone)
           (gslt:rule:scope-match-vector $rule $ambient $site $path $assignment 0 $patterns $rest $targets))
          ($other LNil))))
      ((PCollection $kind $patterns $rest)
       (case $target
         (((PCollection $actual-kind $targets RNone)
           (if (== $kind $actual-kind)
             (gslt:rule:scope-match-bag $rule $ambient $site $path $assignment 0 $patterns $rest $kind $targets)
             LNil))
          ($other LNil))))
      ($other LNil))))

(: gslt:rule:scope-match-arguments (-> Atom Atom Atom Atom Atom Atom Atom Atom %Undefined%))
(= (gslt:rule:scope-match-arguments $rule $ambient $site $path $assignment $index $patterns $targets)
   (case ($patterns $targets)
     (((LNil LNil) (LCons $assignment LNil))
      (((LCons $pattern $tail) (LCons $target $rest))
       (let $nested (gslt:automata:append $path (LCons $index LNil))
         (let $heads (gslt:rule:scope-match $rule $ambient $site $nested $assignment $pattern $target)
           (let $next (+ $index 1)
             (gslt:rule:scope-match-arguments-results $rule $ambient $site $path $heads $next $tail $rest)))))
      ($other LNil))))

(: gslt:rule:scope-match-arguments-results (-> Atom Atom Atom Atom Atom Atom Atom Atom %Undefined%))
(= (gslt:rule:scope-match-arguments-results $rule $ambient $site $path $results $index $patterns $targets)
   (case $results
     ((LNil LNil)
      ((LCons $assignment $rest)
       (let $head (gslt:rule:scope-match-arguments $rule $ambient $site $path $assignment $index $patterns $targets)
         (let $tail (gslt:rule:scope-match-arguments-results $rule $ambient $site $path $rest $index $patterns $targets)
           (gslt:automata:append $head $tail)))))))

(: gslt:rule:scope-match-vector (-> Atom Atom Atom Atom Atom Atom Atom Atom Atom %Undefined%))
(= (gslt:rule:scope-match-vector $rule $ambient $site $path $assignment $index $patterns $rest $targets)
   (case $patterns
     ((LNil
       (case $rest
         ((RNone (case $targets ((LNil (LCons $assignment LNil)) ($other LNil))))
          ((RSome $name)
           (let $nested (gslt:automata:append $path (LCons $index LNil))
             (case (gslt:rule:scope-metadata-capture-rest $rule $ambient $site $nested $assignment $name "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.vec" $targets)
               ((None LNil) ((Some $found) (LCons $found LNil)))))))))
      ((LCons $pattern $tail)
       (case $targets
         (((LCons $target $remaining)
           (let $nested (gslt:automata:append $path (LCons $index LNil))
             (let $heads (gslt:rule:scope-match $rule $ambient $site $nested $assignment $pattern $target)
               (let $next (+ $index 1)
                 (gslt:rule:scope-match-vector-results $rule $ambient $site $path $heads $next $tail $rest $remaining)))))
          ($other LNil)))))))

(: gslt:rule:scope-match-vector-results (-> Atom Atom Atom Atom Atom Atom Atom Atom Atom %Undefined%))
(= (gslt:rule:scope-match-vector-results $rule $ambient $site $path $results $index $patterns $rest $targets)
   (case $results
     ((LNil LNil)
      ((LCons $assignment $remaining)
       (let $head (gslt:rule:scope-match-vector $rule $ambient $site $path $assignment $index $patterns $rest $targets)
         (let $tail (gslt:rule:scope-match-vector-results $rule $ambient $site $path $remaining $index $patterns $rest $targets)
           (gslt:automata:append $head $tail)))))))

(: gslt:rule:scope-match-rule (-> Atom Atom Atom %Undefined%))
(= (gslt:rule:scope-match-rule $rule $ambient $target)
   (case $rule
     (((ScopedRewriteRuleV1 $name $types $premises $left $right (RuleBindingSome $spec))
       (gslt:rule:scope-match $rule $ambient RuleLeft LNil LNil $left $target))
      ($other LNil))))

; Observations of the existing explicit capability and structural zipper.
; Guarded execution remains the original typed rule-job/premise machine.
(: gslt:rule:scope-permitted (-> Atom Atom %Undefined%))
(= (gslt:rule:scope-permitted $permissions $context)
   (case $permissions
     (((OperationalPermissions $enabled $all $slots $lambda $multi $kinds)
       (case $context
         ((ContextHole (== $enabled PermissionYes))
          ((ContextApp $head $before $inner $after)
           (let $index (gslt:automata:length $before)
             (let $slot (TermSlot $head $index)
               (if (== $all PermissionYes)
                 (gslt:rule:scope-permitted $permissions $inner)
                 (if (gslt:automata:member $slot $slots)
                   (gslt:rule:scope-permitted $permissions $inner) False)))))
          ((ContextLam $binder $inner)
           (if (== $lambda PermissionYes)
             (gslt:rule:scope-permitted $permissions $inner) False))
          ((ContextMultiLam $arity $binders $inner)
           (if (== $multi PermissionYes)
             (gslt:rule:scope-permitted $permissions $inner) False))
          ((ContextSubstBody $inner $replacement) False)
          ((ContextSubstReplacement $body $inner) False)
          ((ContextCollection $kind $before $inner $after $rest)
           (if (gslt:automata:member $kind $kinds)
             (if (== $rest RNone)
               (gslt:rule:scope-permitted $permissions $inner) False) False))))))))

(: gslt:rule:scope-fill (-> Atom Atom %Undefined%))
(= (gslt:rule:scope-fill $context $pattern)
   (case $context
     ((ContextHole $pattern)
      ((ContextApp $head $before $inner $after)
       (let $filled (gslt:rule:scope-fill $inner $pattern)
         (let $tail (LCons $filled $after)
           (let $arguments (gslt:automata:append $before $tail)
             (PApp $head $arguments)))))
      ((ContextLam $binder $inner)
       (let $filled (gslt:rule:scope-fill $inner $pattern) (PLam $binder $filled)))
      ((ContextMultiLam $arity $binders $inner)
       (let $filled (gslt:rule:scope-fill $inner $pattern) (PMultiLam $arity $binders $filled)))
      ((ContextSubstBody $inner $replacement)
       (let $filled (gslt:rule:scope-fill $inner $pattern) (PSubst $filled $replacement)))
      ((ContextSubstReplacement $body $inner)
       (let $filled (gslt:rule:scope-fill $inner $pattern) (PSubst $body $filled)))
      ((ContextCollection $kind $before $inner $after $rest)
       (let $filled (gslt:rule:scope-fill $inner $pattern)
         (let $tail (LCons $filled $after)
           (let $arguments (gslt:automata:append $before $tail)
             (PCollection $kind $arguments $rest))))))))

(: gslt:rule:scope-focus-observation (-> Atom Atom Atom Atom Atom Atom Atom Atom %Undefined%))
(= (gslt:rule:scope-focus-observation $ordinal $original $rule $permissions $address $context $source $target)
   (if (gslt:rule:scope-permitted $permissions $context)
     (let $whole-source (gslt:rule:scope-fill $context $source)
       (let $whole-target (gslt:rule:scope-fill $context $target)
         (Some (ScopedFocusObservation $ordinal $original $rule $permissions $address $context
                 $source $target $whole-source $whole-target))))
     None))

; Each cursor denotes an actual residual list occurrence, including equal values.
(: gslt:rule:scope-match-erase-at (-> Atom Atom %Undefined%))
(= (gslt:rule:scope-match-erase-at $index $targets)
   (case $targets
     ((LNil LNil)
      ((LCons $target $tail)
       (if (== $index 0) $tail
         (let $previous (- $index 1)
           (let $remaining (gslt:rule:scope-match-erase-at $previous $tail)
             (LCons $target $remaining))))))))

(: gslt:rule:scope-match-bag (-> Atom Atom Atom Atom Atom Atom Atom Atom Atom Atom %Undefined%))
(= (gslt:rule:scope-match-bag $rule $ambient $site $path $assignment $index $patterns $rest $kind $targets)
   (case $patterns
     ((LNil
       (case $rest
         ((RNone (case $targets ((LNil (LCons $assignment LNil)) ($other LNil))))
          ((RSome $name)
           (let $nested (gslt:automata:append $path (LCons $index LNil))
             (case (gslt:rule:scope-metadata-capture-rest $rule $ambient $site $nested $assignment $name $kind $targets)
               ((None LNil) ((Some $found) (LCons $found LNil)))))))))
      ((LCons $pattern $tail)
       (gslt:rule:scope-match-bag-choices $rule $ambient $site $path $assignment $index $pattern $tail $rest $kind $targets 0)))))

(: gslt:rule:scope-match-bag-results (-> Atom Atom Atom Atom Atom Atom Atom Atom Atom Atom %Undefined%))
(= (gslt:rule:scope-match-bag-results $rule $ambient $site $path $results $index $patterns $rest $kind $targets)
   (case $results
     ((LNil LNil)
      ((LCons $assignment $remaining)
       (let $head (gslt:rule:scope-match-bag $rule $ambient $site $path $assignment $index $patterns $rest $kind $targets)
         (let $tail (gslt:rule:scope-match-bag-results $rule $ambient $site $path $remaining $index $patterns $rest $kind $targets)
           (gslt:automata:append $head $tail)))))))

(: gslt:rule:scope-match-bag-choices (-> Atom Atom Atom Atom Atom Atom Atom Atom Atom Atom Atom Atom %Undefined%))
(= (gslt:rule:scope-match-bag-choices $rule $ambient $site $path $assignment $index $pattern $tail $rest $kind $targets $selected)
   (case (gslt:rule:row-at $selected $targets)
     ((None LNil)
      ((Some $target)
       (let* (($remaining (gslt:rule:scope-match-erase-at $selected $targets))
              ($nested (gslt:automata:append $path (LCons $index LNil)))
              ($heads (gslt:rule:scope-match $rule $ambient $site $nested $assignment $pattern $target))
              ($next (+ $index 1))
              ($first (gslt:rule:scope-match-bag-results $rule $ambient $site $path $heads $next $tail $rest $kind $remaining))
              ($later (+ $selected 1))
              ($more (gslt:rule:scope-match-bag-choices $rule $ambient $site $path $assignment $index $pattern $tail $rest $kind $targets $later)))
         (gslt:automata:append $first $more))))))


; Shared canonical-pattern operations for authored premise execution.
; Free-variable occurrences retain their order and multiplicity. Binder display
; names and collection rest metadata do not change syntactic freshness.
(: gslt:premise:free-vars (-> Atom %Undefined%))
(= (gslt:premise:free-vars $pattern)
   (case $pattern
     (((Var $index) LNil)
      ((FVar $name) (LCons $name LNil))
      ((PApp $head $children) (gslt:premise:free-vars-list $children))
      ((PLam $binder $body) (gslt:premise:free-vars $body))
      ((PMultiLam $arity $binders $body) (gslt:premise:free-vars $body))
      ((PSubst $body $replacement)
       (let* (($left (gslt:premise:free-vars $body))
              ($right (gslt:premise:free-vars $replacement)))
         (gslt:automata:append $left $right)))
      ((PCollection $kind $elements $rest) (gslt:premise:free-vars-list $elements)))))
(: gslt:premise:free-vars-list (-> Atom %Undefined%))
(= (gslt:premise:free-vars-list $patterns)
   (case $patterns
     ((LNil LNil)
      ((LCons $pattern $rest)
       (let* (($left (gslt:premise:free-vars $pattern))
              ($right (gslt:premise:free-vars-list $rest)))
         (gslt:automata:append $left $right))))))
(: gslt:premise:fresh (-> Atom Atom %Undefined%))
(= (gslt:premise:fresh $name $pattern)
   (let $names (gslt:premise:free-vars $pattern)
     (if (gslt:automata:member $name $names) False True)))

; A captured FVar supplies the name; an absent capture retains the literal
; authored name. A non-name capture cannot satisfy a freshness premise.
(: gslt:premise:resolve-name (-> Atom Atom %Undefined%))
(= (gslt:premise:resolve-name $name $bindings)
   (case (gslt:automata:binding $name $bindings)
     ((None (Some $name))
      ((Some $value)
       (case $value
         (((FVar $resolved) (Some $resolved))
          ($non-name None)))))))
(: gslt:premise:freshness (-> Atom Atom Atom %Undefined%))
(= (gslt:premise:freshness $name $term $bindings)
   (case (gslt:premise:resolve-name $name $bindings)
     ((None LNil)
      ((Some $atom)
       (let $subject (gslt:rule:instantiate $term $bindings)
         (if (gslt:premise:fresh $atom $subject)
           (LCons $bindings LNil) LNil))))))

; Lexical parameter operations retain opaque contextual capture values.
(: gslt:premise:scope-remove (-> Atom Atom %Undefined%))
(= (gslt:premise:scope-remove $parameter $assignment)
   (case $assignment
     ((LNil LNil)
      ((LCons (Binding $name $value) $rest)
       (let $tail (gslt:premise:scope-remove $parameter $rest)
         (if (== $name $parameter) $tail
           (let $entry (Binding $name $value) (LCons $entry $tail))))))))

(: gslt:premise:scope-bind (-> Atom Atom Atom %Undefined%))
(= (gslt:premise:scope-bind $parameter $value $assignment)
   (let* (($rest (gslt:premise:scope-remove $parameter $assignment))
          ($entry (Binding $parameter $value)))
     (LCons $entry $rest)))

(: gslt:premise:scope-restore (-> Atom Atom Atom %Undefined%))
(= (gslt:premise:scope-restore $parameter $initial $final)
   (case (gslt:automata:binding $parameter $initial)
     ((None (gslt:premise:scope-remove $parameter $final))
      ((Some $value) (gslt:premise:scope-bind $parameter $value $final)))))

(: gslt:premise:scope-local-value (-> Atom Atom %Undefined%))
(= (gslt:premise:scope-local-value $ambient $pattern)
   (ContextualValue LNil $ambient $pattern))

; An absent value, wrong context, or unresolved rest is refused as None.
(: gslt:premise:scope-collection (-> Atom Atom Atom %Undefined%))
(= (gslt:premise:scope-collection $ambient $assignment $name)
   (case (gslt:automata:binding $name $assignment)
     ((None None)
      ((Some $value)
       (case (gslt:rule:scope-instantiate-value $value $ambient 0 LNil)
         ((None None)
          ((Some $pattern)
           (case $pattern
             (((PCollection $kind $elements RNone)
               (Some (FiniteCollection $kind $elements)))
              ($non-concrete None))))))))))

; Constructor-parameter guards use the authored type and representation.
(: gslt:premise:parameter-type (-> Atom %Undefined%))
(= (gslt:premise:parameter-type $parameter)
   (case $parameter
     (((TermSimple $name $type) (Some $type))
      ((TermAbstraction $binder $name $type)
       (case $type
         (((TArrow $domain $codomain) (Some (TArrow $domain $codomain)))
          ((TBase $sort) (Some (TArrow (TBase $sort) (TBase $sort))))
          ($bad None))))
      ((TermMultiAbstraction $binders $name $type)
       (case $type
         (((TArrow (TMultiBinder $domain) $codomain)
           (Some (TArrow (TMultiBinder $domain) $codomain)))
          ((TBase $sort) (Some (TArrow (TMultiBinder (TBase $sort)) (TBase $sort))))
          ($bad None))))
      ($bad None))))

(: gslt:premise:parameter-representation (-> Atom Atom %Undefined%))
(= (gslt:premise:parameter-representation $parameter $pattern)
   (case $parameter
     (((TermSimple $name $type) True)
      ((TermAbstraction $binder $name $type)
       (case $pattern
         (((PLam BNone $body) True)
          ($bad False))))
      ((TermMultiAbstraction $binders $name $type)
       (case $pattern
         (((PMultiLam $arity LNil $body) True)
          ($bad False))))
      ($bad False))))

; Declaration-derived whole-pattern typing uses the authored declaration view.
(: gslt:premise:type-has (-> Atom Atom Atom Atom Atom %Undefined%))
(= (gslt:premise:type-has $declarations $free $bound $pattern $expected)
   (case $pattern
     (((Var $index)
       (let* (($actual (gslt:rule:row-at $index $bound))
              ($wanted (Some $expected))) (== $actual $wanted)))
      ((FVar $name)
       (let* (($actual (gslt:automata:binding $name $free))
              ($wanted (Some $expected))) (== $actual $wanted)))
      ((PApp $label $arguments)
       (gslt:premise:type-constructors $declarations $free $bound $label $arguments $expected $declarations))
      ((PLam $binder $body)
       (case $expected
         (((TArrow $domain $codomain)
           (let $inner (LCons $domain $bound)
             (gslt:premise:type-has $declarations $free $inner $body $codomain)))
          ($bad False))))
      ((PMultiLam $arity $binders $body)
       (case $expected
         (((TArrow (TMultiBinder $domain) $codomain)
           (let $inner (gslt:premise:type-extend-count $domain $arity $bound)
             (gslt:premise:type-has $declarations $free $inner $body $codomain)))
          ($bad False))))
      ((PSubst $body $replacement) False)
      ((PCollection $kind $elements $rest)
       (case $rest
         ((RNone
           (case $expected
             (((TCollection $actual $element)
               (if (== $actual $kind)
                 (gslt:premise:type-elements $declarations $free $bound $elements $element) False))
              ($base
               (gslt:premise:type-collection-declarations $declarations $free $bound $kind $elements $expected $declarations)))))
          ($bad False))))
      ($bad False))))

(: gslt:premise:type-arguments (-> Atom Atom Atom Atom Atom %Undefined%))
(= (gslt:premise:type-arguments $declarations $free $bound $arguments $parameters)
   (case ($arguments $parameters)
     (((LNil LNil) True)
      (((LCons $argument $arguments-rest) (LCons $parameter $parameters-rest))
       (case (gslt:premise:parameter-type $parameter)
         ((None False)
          ((Some $expected)
           (if (gslt:premise:parameter-representation $parameter $argument)
             (if (gslt:premise:type-has $declarations $free $bound $argument $expected)
               (gslt:premise:type-arguments $declarations $free $bound $arguments-rest $parameters-rest)
               False) False)))))
      ($bad False))))

(: gslt:premise:type-elements (-> Atom Atom Atom Atom Atom %Undefined%))
(= (gslt:premise:type-elements $declarations $free $bound $elements $element)
   (case $elements
     ((LNil True)
      ((LCons $pattern $rest)
       (if (gslt:premise:type-has $declarations $free $bound $pattern $element)
         (gslt:premise:type-elements $declarations $free $bound $rest $element) False)))))

(: gslt:premise:type-constructors (-> Atom Atom Atom Atom Atom Atom Atom %Undefined%))
(= (gslt:premise:type-constructors $declarations $free $bound $label $arguments $expected $remaining)
   (case $remaining
     ((LNil False)
      ((LCons (GrammarTypingV1 $actual $category $parameters) $rest)
       (if (== $actual $label)
         (let $result (TBase $category)
           (if (== $expected $result)
             (case $parameters
               (((LCons (TermSimple $parameter (TCollection $kind $element)) LNil)
                 (gslt:premise:type-constructors $declarations $free $bound $label $arguments $expected $rest))
                ($ordinary
                 (if (gslt:premise:type-arguments $declarations $free $bound $arguments $parameters)
                   True
                   (gslt:premise:type-constructors $declarations $free $bound $label $arguments $expected $rest)))))
             (gslt:premise:type-constructors $declarations $free $bound $label $arguments $expected $rest)))
         (gslt:premise:type-constructors $declarations $free $bound $label $arguments $expected $rest)))
      ((LCons (GrammarTypingWrappedV1 $actual $category $parameters) $rest)
       (if (== $actual $label)
         (let $result (TBase $category)
           (if (== $expected $result)
             (if (gslt:premise:type-arguments $declarations $free $bound $arguments $parameters)
               True
               (gslt:premise:type-constructors $declarations $free $bound $label $arguments $expected $rest))
             (gslt:premise:type-constructors $declarations $free $bound $label $arguments $expected $rest)))
         (gslt:premise:type-constructors $declarations $free $bound $label $arguments $expected $rest))))))

(: gslt:premise:type-collection-declarations (-> Atom Atom Atom Atom Atom Atom Atom %Undefined%))
(= (gslt:premise:type-collection-declarations $declarations $free $bound $kind $elements $expected $remaining)
   (case $remaining
     ((LNil False)
      ((LCons (GrammarTypingV1 $label $category $parameters) $rest)
       (case ($parameters $expected)
         ((((LCons (TermSimple $parameter (TCollection $actual $element)) LNil) (TBase $sort))
           (if (== $category $sort)
             (if (== $actual $kind)
               (if (gslt:premise:type-elements $declarations $free $bound $elements $element) True
                 (gslt:premise:type-collection-declarations $declarations $free $bound $kind $elements $expected $rest))
               (gslt:premise:type-collection-declarations $declarations $free $bound $kind $elements $expected $rest))
             (gslt:premise:type-collection-declarations $declarations $free $bound $kind $elements $expected $rest)))
          ($ordinary
           (gslt:premise:type-collection-declarations $declarations $free $bound $kind $elements $expected $rest)))))
      ((LCons (GrammarTypingWrappedV1 $label $category $parameters) $rest)
       (gslt:premise:type-collection-declarations $declarations $free $bound $kind $elements $expected $rest)))))

(: gslt:premise:type-extend-count (-> Atom Number Atom %Undefined%))
(= (gslt:premise:type-extend-count $domain $count $bound)
   (if (== $count 0) $bound
     (let* (($previous (- $count 1))
            ($tail (gslt:premise:type-extend-count $domain $previous $bound)))
       (LCons $domain $tail))))

; Open-object admission keeps typing, binder metadata, object form and scope distinct.
(: gslt:premise:object-pattern (-> Atom %Undefined%))
(= (gslt:premise:object-pattern $pattern)
   (case $pattern
     (((Var $index) True)
      ((FVar $name) True)
      ((PApp $label $arguments) (gslt:premise:object-patterns $arguments))
      ((PLam $binder $body) (gslt:premise:object-pattern $body))
      ((PMultiLam $arity $binders $body) (gslt:premise:object-pattern $body))
      ((PSubst $body $replacement) False)
      ((PCollection $kind $elements RNone) (gslt:premise:object-patterns $elements))
      ($bad False))))

(: gslt:premise:object-patterns (-> Atom %Undefined%))
(= (gslt:premise:object-patterns $patterns)
   (case $patterns
     ((LNil True)
      ((LCons $pattern $rest)
       (if (gslt:premise:object-pattern $pattern)
         (gslt:premise:object-patterns $rest) False))
      ($bad False))))

(: gslt:premise:canonical-binders (-> Atom %Undefined%))
(= (gslt:premise:canonical-binders $pattern)
   (case $pattern
     (((Var $index) True)
      ((FVar $name) True)
      ((PApp $label $arguments) (gslt:premise:canonical-binders-list $arguments))
      ((PLam BNone $body) (gslt:premise:canonical-binders $body))
      ((PMultiLam $arity LNil $body) (gslt:premise:canonical-binders $body))
      ((PSubst $body $replacement)
       (if (gslt:premise:canonical-binders $body)
         (gslt:premise:canonical-binders $replacement) False))
      ((PCollection $kind $elements $rest) (gslt:premise:canonical-binders-list $elements))
      ($bad False))))

(: gslt:premise:canonical-binders-list (-> Atom %Undefined%))
(= (gslt:premise:canonical-binders-list $patterns)
   (case $patterns
     ((LNil True)
      ((LCons $pattern $rest)
       (if (gslt:premise:canonical-binders $pattern)
         (gslt:premise:canonical-binders-list $rest) False))
      ($bad False))))

(: gslt:premise:open-well-sorted (-> Atom Atom Atom Atom Atom %Undefined%))
(= (gslt:premise:open-well-sorted $declarations $free $bound $expected $pattern)
   (if (gslt:premise:type-has $declarations $free $bound $pattern $expected)
     (if (gslt:premise:canonical-binders $pattern)
       (if (gslt:premise:object-pattern $pattern)
         (let $depth (gslt:automata:length $bound)
           (gslt:rule:scope-well-scoped $depth $pattern)) False) False) False))


; Whole stored assignments use the authored dependency and ambient contexts.
(: gslt:premise:type-context-lookup (-> Atom Atom %Undefined%))
(= (gslt:premise:type-context-lookup $name $context)
   (case $context
     ((LNil None)
      ((LCons (TypeBinding $declared $type) $rest)
       (if (== $declared $name) (Some $type)
         (gslt:premise:type-context-lookup $name $rest)))
      ($bad None))))

(: gslt:premise:check-assignment (-> Atom Atom Atom Atom Atom Atom %Undefined%))
(=
  (gslt:premise:check-assignment $declarations $free $bound $rule $spec $assignment)
  (case
    $assignment
    ((LNil True)
     ((LCons (Binding $name (ContextualValue $actualDependencies $ambient $body)) $rest)
      (case
        (gslt:rule:scope-metadata-dependencies $spec $name)
        ((None False)
         ((Some $dependencies)
          (case
            $rule
            (((ScopedRewriteRuleV1 $ruleName $types $premises $left $right $bindings)
              (case
                (gslt:premise:type-context-lookup $name $types)
                ((None False)
                 ((Some $expected)
                  (let*
                    (($actualAmbient (gslt:automata:length $bound))
                     ($bodyBound (gslt:automata:append $dependencies $bound)))
                    (if
                      (== $actualDependencies $dependencies)
                      (if
                        (== $ambient $actualAmbient)
                        (if
                          (gslt:premise:object-pattern $body)
                          (if
                            (gslt:premise:type-has $declarations $free $bodyBound $body $expected)
                            (gslt:premise:check-assignment
                              $declarations
                              $free
                              $bound
                              $rule
                              $spec
                              $rest)
                            False)
                          False)
                        False)
                      False))))))
             ($badRule False)))))))
     ($bad False))))


; Transitions retain the original typed premise-machine data. Unsupported
; operational forms return None for suspension at this partial entry.
(: gslt:premise:context-next (-> Atom %Undefined%))
(= (gslt:premise:context-next $context)
   (case $context
     (((PremiseContext $index $rule $spec $bound $premise $quantifiers)
       (let $next (+ $premise 1)
         (PremiseContext $index $rule $spec $bound $next 0)))
      ($bad None))))

(: gslt:premise:context-quantified (-> Atom %Undefined%))
(= (gslt:premise:context-quantified $context)
   (case $context
     (((PremiseContext $index $rule $spec $bound $premise $quantifiers)
       (let $next (+ $quantifiers 1)
         (PremiseContext $index $rule $spec $bound $premise $next)))
      ($bad None))))

(: gslt:premise:machine-deliver (-> Atom Atom %Undefined%))
(= (gslt:premise:machine-deliver $result $continuation)
   (case $continuation
     (((PremiseDone $outer)
       (Some (PremiseExpansion LNil (LCons $result LNil) LNil)))
      ((PremiseNext $context $premise $premises $initial $tail)
       (case $result
         (((PremiseResult $goal (PremiseAnswer $assignment $event))
           (let $next (gslt:premise:context-next $context)
             (Some (PremiseExpansion
               (LCons (PremiseEvaluate (PremisesGoal $next $premises $assignment)
                 (PremisePrepend $context $premise $premises $initial $assignment $event $tail)) LNil)
               LNil LNil))))
          ($badResult None))))
      ((PremisePrepend $context $premise $premises $initial $middle $event $tail)
       (case $result
         (((PremiseResult $goal (PremisesAnswer $assignment $events))
           (Some (PremiseExpansion
             (LCons (PremiseDeliver
               (PremiseResult (PremisesGoal $context (LCons $premise $premises) $initial)
                 (PremisesAnswer $assignment (LCons $event $events))) $tail) LNil)
             LNil LNil)))
          ($badResult None))))
      ((PremiseQuantifier $context $collection $parameter $body $initial $kind $elements $tail)
       (case $result
         (((PremiseResult $goal (QuantifiedAnswer $assignment $events))
           (case $context
             (((PremiseContext $index $rule $spec $bound $premise $quantifiers)
               (Some (PremiseExpansion
                 (LCons (PremiseDeliver
                   (PremiseResult (PremiseGoal $context (ForAll $collection $parameter $body) $initial)
                     (PremiseAnswer $assignment (PremiseQuantifiedEvent $premise $quantifiers $kind $events)))
                   $tail) LNil) LNil LNil)))
              ($badContext None))))
          ($badResult None))))
      ((PremiseElement $context $parameter $body $index $element $elements $initial $tail)
       (case $result
         (((PremiseResult $goal (PremiseAnswer $assignment $event))
           (let* (($restored $initial)
                  ($next (+ $index 1)))
             (Some (PremiseExpansion
               (LCons (PremiseEvaluate
                 (QuantifiedGoal $context $parameter $body $next $elements $restored)
                 (PremisePrependElement $context $parameter $body $index $element $elements
                   $initial $assignment $event $tail)) LNil) LNil LNil))))
          ($badResult None))))
      ((PremisePrependElement $context $parameter $body $index $element $elements $initial $middle $event $tail)
       (case $result
         (((PremiseResult $goal (QuantifiedAnswer $assignment $events))
           (Some (PremiseExpansion
             (LCons (PremiseDeliver
               (PremiseResult (QuantifiedGoal $context $parameter $body $index (LCons $element $elements) $initial)
                 (QuantifiedAnswer $assignment
                   (LCons (QuantifiedElement $index $element (LCons $event LNil)) $events)))
               $tail) LNil) LNil LNil)))
          ($badResult None))))
      ((PremiseSearchedRoot $bound $type $source $index $limit $tail)
       (case $result
         (((PremiseResult $goal (RootAnswer $trace $captured $completed $events $target))
           (Some (PremiseExpansion
             (LCons (PremiseDeliver
               (PremiseResult (StepsGoal $bound $type $source $limit)
                 (StepsAnswer $index $trace $captured $completed $events $target)) $tail) LNil)
             LNil LNil)))
          ($badResult None))))
      ($unsupported None))))

(: gslt:premise:machine-evaluate (-> Atom Atom Atom Atom %Undefined%))
(= (gslt:premise:machine-evaluate $declarations $free $goal $continuation)
   (case $goal
     (((PremisesGoal $context $premises $initial)
       (case $premises
         ((LNil
           (Some (PremiseExpansion
             (LCons (PremiseDeliver (PremiseResult $goal (PremisesAnswer $initial LNil)) $continuation) LNil)
             LNil LNil)))
          ((LCons $premise $rest)
           (Some (PremiseExpansion
             (LCons (PremiseEvaluate (PremiseGoal $context $premise $initial)
               (PremiseNext $context $premise $rest $initial $continuation)) LNil) LNil LNil)))
          ($badPremises None))))
      ((QuantifiedGoal $context $parameter $body $index $elements $initial)
       (case $elements
         ((LNil
           (Some (PremiseExpansion
             (LCons (PremiseDeliver (PremiseResult $goal (QuantifiedAnswer $initial LNil)) $continuation) LNil)
             LNil LNil)))
          ((LCons $element $rest)
           (case $context
             (((PremiseContext $ruleIndex $rule $spec $bound $premise $quantifiers)
               (let* (($ambient (gslt:automata:length $bound))
                      ($local (gslt:premise:scope-local-value $ambient $element))
                      ($assignment (gslt:premise:scope-bind $parameter $local $initial))
                      ($quantified (gslt:premise:context-quantified $context)))
                 (if (gslt:premise:check-assignment $declarations $free $bound $rule $spec $assignment)
                   (Some (PremiseExpansion
                     (LCons (PremiseEvaluate (PremiseGoal $quantified $body $assignment)
                       (PremiseElement $context $parameter $body $index $element $rest $initial $continuation)) LNil)
                     LNil LNil))
                   (Some (PremiseExpansion LNil LNil
                     (LCons (PremiseQuantifiedAssignment $premise $quantifiers $index) LNil))))))
              ($badContext None))))
          ($badElements None))))
      ((PremiseGoal $context (ForAll $collection $parameter $body) $initial)
       (case $context
         (((PremiseContext $index $rule $spec $bound $premise $quantifiers)
           (let $ambient (gslt:automata:length $bound)
             (case (gslt:premise:scope-collection $ambient $initial $collection)
               ((None
                 (Some (PremiseExpansion LNil LNil
                   (LCons (PremiseCollectionProjection $premise $quantifiers $collection) LNil))))
                ((Some (FiniteCollection $kind $elements))
                 (Some (PremiseExpansion
                   (LCons (PremiseEvaluate (QuantifiedGoal $context $parameter $body 0 $elements $initial)
                     (PremiseQuantifier $context $collection $parameter $body $initial $kind $elements $continuation)) LNil)
                   LNil LNil)))))))
          ($badContext None))))
      ((StepsGoal $bound $type $source $limit)
       (Some (PremiseExpansion
         (LCons (PremiseScanChildren $bound $type $source $limit 0 $continuation) LNil) LNil LNil)))
      ($unsupported None))))

(: gslt:premise:machine-expand (-> Atom Atom Atom %Undefined%))
(= (gslt:premise:machine-expand $declarations $free $task)
   (case $task
     (((PremiseEvaluate $goal $continuation)
       (gslt:premise:machine-evaluate $declarations $free $goal $continuation))
      ((PremiseDeliver $result $continuation)
       (gslt:premise:machine-deliver $result $continuation))
      ((PremiseScanChildren $bound $type $source $limit $cursor $continuation)
       (if (< $cursor $limit)
         (let $next (+ $cursor 1) (Some (PremiseExpansion
           (LCons (PremiseEvaluate (RootGoal $bound $type $source $cursor)
             (PremiseSearchedRoot $bound $type $source $cursor $limit $continuation))
             (LCons (PremiseScanChildren $bound $type $source $limit $next $continuation) LNil))
           LNil LNil)))
         (Some (PremiseExpansion LNil LNil LNil))))
      ($unsupported None))))


; Finite operational projections preserve physical declaration occurrences.
(: gslt:premise:constructor-declarations (-> Atom Atom %Undefined%))
(= (gslt:premise:constructor-declarations $constructor $declarations)
   (case $declarations
     ((LNil LNil)
      ((LCons (GrammarTypingV1 $label $category $parameters) $rest)
       (if (== $label $constructor)
         (let $filtered (gslt:premise:constructor-declarations $constructor $rest)
           (LCons (GrammarTypingV1 $label $category $parameters) $filtered))
         (gslt:premise:constructor-declarations $constructor $rest)))
      ((LCons (GrammarTypingWrappedV1 $label $category $parameters) $rest)
       (if (== $label $constructor)
         (let $filtered (gslt:premise:constructor-declarations $constructor $rest)
           (LCons (GrammarTypingWrappedV1 $label $category $parameters) $filtered))
         (gslt:premise:constructor-declarations $constructor $rest)))
      ($bad LNil))))

(: gslt:premise:source-type (-> Atom Atom Atom %Undefined%))
(= (gslt:premise:source-type $declarations $rule $source)
   (case $source
     (((FVar $name)
       (case $rule
         (((ScopedRewriteRuleV1 $ruleName $types $premises $left $right $bindings)
           (gslt:premise:type-context-lookup $name $types))
          ($badRule None))))
      ((PApp $constructor $arguments)
       (case (gslt:premise:constructor-declarations $constructor $declarations)
         (((LCons (GrammarTypingV1 $label $category $parameters) LNil)
           (Some (TBase $category)))
          ((LCons (GrammarTypingWrappedV1 $label $category $parameters) LNil)
           (Some (TBase $category)))
          ($ambiguous None))))
      ($unavailable None))))

(: gslt:premise:specification (-> Atom Atom %Undefined%))
(= (gslt:premise:specification $index $specifications)
   (case $specifications
     ((LNil None)
      ((LCons (PremiseSpecification $position $spec) $rest)
       (if (== $position $index) (Some $spec)
         (gslt:premise:specification $index $rest)))
      ($bad None))))

(: gslt:premise:signature-candidates (-> Atom Atom Atom %Undefined%))
(= (gslt:premise:signature-candidates $relation $arity $signatures)
   (case $signatures
     ((LNil LNil)
      ((LCons (PremiseSignature $declared $types $modes) $rest)
       (if (== $declared $relation)
         (let $count (gslt:automata:length $types)
           (if (== $count $arity)
             (let $filtered (gslt:premise:signature-candidates $relation $arity $rest)
               (LCons (PremiseSignature $declared $types $modes) $filtered))
             (gslt:premise:signature-candidates $relation $arity $rest)))
         (gslt:premise:signature-candidates $relation $arity $rest)))
      ($bad LNil))))

(: gslt:premise:signature (-> Atom Atom Atom %Undefined%))
(= (gslt:premise:signature $relation $arity $provider)
   (case $provider
     (((PremiseProvider $signatures $rows)
       (case (gslt:premise:signature-candidates $relation $arity $signatures)
         (((LCons (PremiseSignature $declared $types $modes) LNil)
           (let $count (gslt:automata:length $modes)
             (if (== $count $arity)
               (Some (PremiseSignature $declared $types $modes)) None)))
          ($unavailable None))))
      ($bad None))))

(: gslt:premise:check-values (-> Atom Atom Atom Atom Atom %Undefined%))
(= (gslt:premise:check-values $declarations $free $bound $values $types)
   (case $values
     ((LNil
       (case $types ((LNil True) ($mismatch False))))
      ((LCons $value $restValues)
       (case $types
         (((LCons $type $restTypes)
           (if (gslt:premise:open-well-sorted $declarations $free $bound $type $value)
             (gslt:premise:check-values $declarations $free $bound $restValues $restTypes) False))
          ($mismatch False))))
      ($bad False))))

(: gslt:premise:check-row (-> Atom Atom Atom Atom Atom %Undefined%))
(= (gslt:premise:check-row $declarations $free $bound $signature $row)
   (case $signature
     (((PremiseSignature $declared $types $modes)
       (case $row
         (((PremiseProviderRow $relation $values)
           (if (== $relation $declared)
             (gslt:premise:check-values $declarations $free $bound $values $types) False))
          ($badRow False))))
      ($badSignature False))))


(: gslt:premise:ground-at (-> Atom Atom %Undefined%))
(= (gslt:premise:ground-at $depth $pattern)
   (case $pattern
     (((Var $index) (< $index $depth))
      ((FVar $name) False)
      ((PApp $head $children) (gslt:premise:ground-list-at $depth $children))
      ((PLam $binder $body)
       (let $next (+ $depth 1) (gslt:premise:ground-at $next $body)))
      ((PMultiLam $arity $binders $body)
       (let $next (+ $depth $arity) (gslt:premise:ground-at $next $body)))
      ((PSubst $body $replacement)
       (let $next (+ $depth 1)
         (if (gslt:premise:ground-at $next $body)
           (gslt:premise:ground-at $depth $replacement) False)))
      ((PCollection $kind $elements $rest)
       (case $rest
         ((RNone (gslt:premise:ground-list-at $depth $elements))
          ($open False))))
      ($invalid False))))

(: gslt:premise:ground-list-at (-> Atom Atom %Undefined%))
(= (gslt:premise:ground-list-at $depth $patterns)
   (case $patterns
     ((LNil True)
      ((LCons $pattern $rest)
       (if (gslt:premise:ground-at $depth $pattern)
         (gslt:premise:ground-list-at $depth $rest) False))
      ($invalid False))))


(: gslt:premise:reflective-rules (-> Atom Atom %Undefined%))
(= (gslt:premise:reflective-rules $requested $declarations)
   (case $declarations
     ((LNil LNil)
      ((LCons (ReflectiveRule $name $rewrite $matching $substitution) $rest)
       (if (== $rewrite $requested)
         (let $filtered (gslt:premise:reflective-rules $requested $rest)
           (LCons (ReflectiveRule $name $rewrite $matching $substitution) $filtered))
         (gslt:premise:reflective-rules $requested $rest)))
      ($bad LNil))))

(: gslt:premise:reflective-presentations (-> Atom Atom %Undefined%))
(= (gslt:premise:reflective-presentations $requested $declarations)
   (case $declarations
     ((LNil LNil)
      ((LCons (ReflectivePresentation $name $processSort $nameSort $quote $drop $kind $unit $equation $scope) $rest)
       (if (== $name $requested)
         (let $filtered (gslt:premise:reflective-presentations $requested $rest)
           (LCons (ReflectivePresentation $name $processSort $nameSort $quote $drop $kind $unit $equation $scope) $filtered))
         (gslt:premise:reflective-presentations $requested $rest)))
      ($bad LNil))))

(: gslt:premise:presentation-named (-> Atom Atom %Undefined%))
(= (gslt:premise:presentation-named $presentations $requested)
   (case (gslt:premise:reflective-presentations $requested $presentations)
     (((LCons (ReflectivePresentation $name $processSort $nameSort $quote $drop $kind $unit $equation $scope) LNil)
       (Some (ReflectivePresentation $name $processSort $nameSort $quote $drop $kind $unit $equation $scope)))
      ($unavailable None))))

(: gslt:premise:substitution-presentation (-> Atom Atom %Undefined%))
(= (gslt:premise:substitution-presentation $profile $rule)
   (case $profile
     (((PremiseReflection $presentations $declarations)
       (case $rule
         (((ScopedRewriteRuleV1 $ruleName $types $premises $left $right $bindings)
           (case (gslt:premise:reflective-rules $ruleName $declarations)
             (((LCons (ReflectiveRule $name $rewrite $matching $substitution) LNil)
               (gslt:premise:presentation-named $presentations $substitution))
              ($unavailable None))))
          ($badRule None))))
      ($badProfile None))))


(: gslt:premise:query-site (-> Atom Atom %Undefined%))
(= (gslt:premise:query-site $context $argument)
   (case $context
     (((PremiseContext $ruleIndex $rule $spec $bound $premise $quantifiers)
       (RulePremise $premise $quantifiers $argument))
      ($bad None))))

(: gslt:premise:query-matching-request (-> Atom Atom Atom Atom Atom %Undefined%))
(= (gslt:premise:query-matching-request $context $index $assignment $schema $value)
   (case $context
     (((PremiseContext $ruleIndex $rule $spec $bound $premise $quantifiers)
       (let* (($ambient (gslt:automata:length $bound))
              ($site (gslt:premise:query-site $context $index)))
         (ScopedMatcherRequest $rule $spec $ambient $site LNil 0 $assignment $schema $value)))
      ($bad None))))

(: gslt:premise:query-expand-in (-> Atom Atom Atom %Undefined%))
(= (gslt:premise:query-expand-in $environment $request $task) (case (gslt:premise:matching-environment $environment) (((PremiseEnvironment $declarations $rewrites $specifications (PremiseProvider $signatures $rows) $reflection $free) (case $request (((PremiseQueryRequest (PremiseContext $ruleIndex $rule $spec $bound $premise $quantifiers) $relation $arguments $initial) (case $task ((PremiseQueryStart (let $arity (gslt:automata:length $arguments) (case (gslt:premise:signature $relation $arity (PremiseProvider $signatures $rows)) ((None (Some (PremiseExpansion LNil LNil (LCons (PremiseSignatureUnavailable $relation $arity) LNil)))) ((Some $signature) (Some (PremiseExpansion (LCons (PremiseQueryRows $signature 0) LNil) LNil LNil))) ($badSignature None))))) ((PremiseQueryRows $signature $cursor) (case (gslt:rule:row-at $cursor $rows) ((None (Some (PremiseExpansion LNil LNil LNil))) ((Some (PremiseProviderRow $rowRelation $values)) (case $signature (((PremiseSignature $signatureRelation $types $modes) (let* (($next (+ $cursor 1)) ($checked (gslt:premise:check-row $declarations $free $bound $signature (PremiseProviderRow $rowRelation $values)))) (if $checked (Some (PremiseExpansion (LCons (PremiseQueryArguments $cursor 0 $initial $arguments $values $modes LNil) (LCons (PremiseQueryRows $signature $next) LNil)) LNil LNil)) (Some (PremiseExpansion (LCons (PremiseQueryRows $signature $next) LNil) LNil LNil))))) ($badSignature None)))) ($badRow None)))) ((PremiseQueryArguments $rowIndex $index $assignment LNil LNil LNil $origins) (if (gslt:premise:check-assignment $declarations $free $bound $rule $spec $assignment) (Some (PremiseExpansion LNil (LCons (PremiseQueryAnswer $rowIndex $assignment $origins) LNil) LNil)) (Some (PremiseExpansion LNil LNil LNil)))) ((PremiseQueryArguments $rowIndex $index $assignment (LCons $schema $schemas) (LCons $value $values) (LCons RelationInput $modes) $origins) (let* (($ambient (gslt:automata:length $bound)) ($site (RulePremise $premise $quantifiers $index))) (case (gslt:rule:scope-instantiate-at None $rule $spec $ambient $site LNil 0 $assignment $schema) ((None (Some (PremiseExpansion LNil LNil (LCons (PremiseInputUnavailable $rowIndex $index) LNil)))) ((Some $actual) (if (gslt:premise:matching-input $environment $actual $value) (let* (($next (+ $index 1)) ($extended (gslt:automata:append $origins (LCons (ArgumentOrigin $index LNil) LNil)))) (Some (PremiseExpansion (LCons (PremiseQueryArguments $rowIndex $next $assignment $schemas $values $modes $extended) LNil) LNil LNil))) (Some (PremiseExpansion LNil LNil LNil)))) ($badInstantiation None))))) ((PremiseQueryArguments $rowIndex $index $assignment (LCons $schema $schemas) (LCons $value $values) (LCons RelationOutput $modes) $origins) (let* (($query (gslt:premise:query-matching-request (PremiseContext $ruleIndex $rule $spec $bound $premise $quantifiers) $index $assignment $schema $value)) ($started (gslt:premise:matching-start $environment $query))) (Some (PremiseExpansion (LCons (PremiseQueryMatcher $rowIndex $index $schemas $values $modes $origins $query $started 0) LNil) LNil LNil)))) ((PremiseQueryArguments $rowIndex $index $assignment $schemas $values $modes $origins) (Some (PremiseExpansion LNil LNil (LCons (PremiseArgumentShape $rowIndex $index) LNil)))) ((PremiseQueryMatcher $rowIndex $argument $schemas $values $modes $origins $query $state $cursor) (case (gslt:premise:matching-answer-at $environment $state $cursor) (((Some (ScopedMatcherAnswer $assignment $trace)) (let* (($nextArgument (+ $argument 1)) ($nextCursor (+ $cursor 1)) ($extended (gslt:automata:append $origins (LCons (ArgumentOrigin $argument $trace) LNil)))) (Some (PremiseExpansion (LCons (PremiseQueryArguments $rowIndex $nextArgument $assignment $schemas $values $modes $extended) (LCons (PremiseQueryMatcher $rowIndex $argument $schemas $values $modes $origins $query $state $nextCursor) LNil)) LNil LNil)))) (None (if (gslt:premise:matching-complete $environment $state) (Some (PremiseExpansion LNil LNil LNil)) (let $stepped (gslt:premise:matching-tick $environment $query $state) (Some (PremiseExpansion (LCons (PremiseQueryMatcher $rowIndex $argument $schemas $values $modes $origins $query $stepped $cursor) LNil) LNil LNil))))) ($badAnswer None)))) ($badTask None)))) ($badRequest None)))) ($badEnvironment None))))


; Original scoped matcher tasks and physical choice histories.
; The explicit request specification and depth are data of the source machine.

(: gslt:rule:scope-matcher-capture (-> Atom Atom Atom Atom Atom Atom Atom Atom Atom %Undefined%))
(= (gslt:rule:scope-matcher-capture $rule $spec $ambient $site $path $depth $assignment $name $target)
   (case (gslt:rule:scope-metadata-dependencies $spec $name)
     (((Some $dependencies)
       (case (gslt:rule:scope-metadata-arguments $rule $spec $name $site $path)
         (((Some $arguments)
           (case (gslt:rule:scope-recover-value $dependencies $ambient $depth $arguments $target)
             (((Some $value) (gslt:rule:scope-assign $assignment $name $value))
              ($failed None))))
          ($no-arguments None))))
      ($no-dependencies None))))

(: gslt:rule:scope-matcher-captured-work (-> Atom %Undefined%))
(= (gslt:rule:scope-matcher-captured-work $captured)
   (case $captured
     ((None LNil)
      ((Some $assignment) (LCons (ScopedMatcherWork $assignment LNil LNil) LNil)))))

(: gslt:rule:scope-matcher-split-at (-> Atom Atom %Undefined%))
(= (gslt:rule:scope-matcher-split-at $count $values)
   (if (== $count 0) (ScopedMatcherSplit LNil $values)
     (case $values
       ((LNil (ScopedMatcherSplit LNil LNil))
        ((LCons $head $tail)
         (let $previous (- $count 1)
           (case (gslt:rule:scope-matcher-split-at $previous $tail)
             (((ScopedMatcherSplit $front $back) (ScopedMatcherSplit (LCons $head $front) $back))))))))))

(: gslt:rule:scope-matcher-start (-> Atom %Undefined%))
(= (gslt:rule:scope-matcher-start $request)
   (case $request
     (((ScopedMatcherRequest $rule $spec $ambient $site $path $depth $initial $schema $target)
       (ScopedMatcherState
         (LCons (ScopedMatcherWork $initial (LCons (ScopedMatcherTree $path $depth $schema $target) LNil) LNil) LNil)
         LNil)))))

(: gslt:rule:scope-matcher-complete (-> Atom %Undefined%))
(= (gslt:rule:scope-matcher-complete $state)
   (case $state
     (((ScopedMatcherState $agenda $answers)
       (case $agenda ((LNil True) ((LCons $work $rest) False)))))))

(: gslt:rule:scope-matcher-expand-tree (-> Atom Atom Atom Atom Atom Atom Atom Atom Atom %Undefined%))
(= (gslt:rule:scope-matcher-expand-tree $rule $spec $ambient $site $assignment $path $depth $schema $target)
   (case $schema
     (((FVar $name)
       (let $captured (gslt:rule:scope-matcher-capture $rule $spec $ambient $site $path $depth $assignment $name $target)
         (gslt:rule:scope-matcher-captured-work $captured)))
      ((Var $expected)
       (case $target
         (((Var $actual) (if (== $expected $actual) (LCons (ScopedMatcherWork $assignment LNil LNil) LNil) LNil))
          ($other LNil))))
      ((PApp $label $patterns)
       (case $target
         (((PApp $actual $targets)
           (if (== $label $actual)
             (LCons (ScopedMatcherWork $assignment (LCons (ScopedMatcherArguments $path $depth 0 $patterns $targets) LNil) LNil) LNil)
             LNil))
          ($other LNil))))
      ((PLam $display $body)
       (case $target
         (((PLam $actual-display $actual-body)
           (let* (($nested (gslt:automata:append $path (LCons 0 LNil))) ($deeper (+ $depth 1)))
             (LCons (ScopedMatcherWork $assignment (LCons (ScopedMatcherTree $nested $deeper $body $actual-body) LNil) LNil) LNil)))
          ($other LNil))))
      ((PMultiLam $arity $display $body)
       (case $target
         (((PMultiLam $actual-arity $actual-display $actual-body)
           (if (== $arity $actual-arity)
             (let* (($nested (gslt:automata:append $path (LCons 0 LNil))) ($deeper (+ $depth $arity)))
               (LCons (ScopedMatcherWork $assignment (LCons (ScopedMatcherTree $nested $deeper $body $actual-body) LNil) LNil) LNil))
             LNil))
          ($other LNil))))
      ((PSubst $body $replacement)
       (case $target
         (((PSubst $actual-body $actual-replacement)
           (let* (($body-path (gslt:automata:append $path (LCons 0 LNil)))
                  ($replacement-path (gslt:automata:append $path (LCons 1 LNil))) ($deeper (+ $depth 1)))
             (LCons (ScopedMatcherWork $assignment
               (LCons (ScopedMatcherTree $body-path $deeper $body $actual-body)
                 (LCons (ScopedMatcherTree $replacement-path $depth $replacement $actual-replacement) LNil)) LNil) LNil)))
          ($other LNil))))
      ((PCollection $kind $patterns $rest)
       (case $target
         (((PCollection $actual-kind $targets RNone)
           (if (== $kind $actual-kind)
             (if (== $kind "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.vec")
               (case $rest
                 ((RNone (LCons (ScopedMatcherWork $assignment
                    (LCons (ScopedMatcherArguments $path $depth 0 $patterns $targets) LNil) LNil) LNil))
                  ((RSome $name)
                   (let $length (gslt:automata:length $patterns)
                     (case (gslt:rule:scope-matcher-split-at $length $targets)
                       (((ScopedMatcherSplit $front $back)
                         (let $nested (gslt:automata:append $path (LCons $length LNil))
                           (LCons (ScopedMatcherWork $assignment
                             (LCons (ScopedMatcherArguments $path $depth 0 $patterns $front)
                               (LCons (ScopedMatcherRestCapture $nested $depth $name $kind $back) LNil)) LNil) LNil)))))))))
               (LCons (ScopedMatcherWork $assignment
                 (LCons (ScopedMatcherBag $path $depth 0 $patterns $rest $kind $targets) LNil) LNil) LNil))
             LNil))
          ($other LNil))))
      ($other LNil))))

(: gslt:rule:scope-matcher-expand (-> Atom Atom Atom %Undefined%))
(= (gslt:rule:scope-matcher-expand $request $assignment $task)
   (case $request
     (((ScopedMatcherRequest $rule $spec $ambient $site $request-path $request-depth $initial $schema $target)
       (case $task
         (((ScopedMatcherTree $path $depth $pattern $value)
           (gslt:rule:scope-matcher-expand-tree $rule $spec $ambient $site $assignment $path $depth $pattern $value))
          ((ScopedMatcherArguments $path $depth $index $patterns $targets)
           (case ($patterns $targets)
             (((LNil LNil) (LCons (ScopedMatcherWork $assignment LNil LNil) LNil))
              (((LCons $pattern $tail) (LCons $value $remaining))
               (let* (($nested (gslt:automata:append $path (LCons $index LNil))) ($next (+ $index 1)))
                 (LCons (ScopedMatcherWork $assignment
                   (LCons (ScopedMatcherTree $nested $depth $pattern $value)
                     (LCons (ScopedMatcherArguments $path $depth $next $tail $remaining) LNil)) LNil) LNil)))
              ($other LNil))))
          ((ScopedMatcherBag $path $depth $index $patterns $rest $kind $targets)
           (case $patterns
             ((LNil
               (case $rest
                 ((RNone (case $targets ((LNil (LCons (ScopedMatcherWork $assignment LNil LNil) LNil)) ($other LNil))))
                  ((RSome $name)
                   (let $nested (gslt:automata:append $path (LCons $index LNil))
                     (LCons (ScopedMatcherWork $assignment
                       (LCons (ScopedMatcherRestCapture $nested $depth $name $kind $targets) LNil) LNil) LNil))))))
              ((LCons $pattern $tail)
               (LCons (ScopedMatcherWork $assignment
                 (LCons (ScopedMatcherBagSelect $path $depth $index $pattern $tail $rest $kind $targets 0) LNil) LNil) LNil)))))
          ((ScopedMatcherBagSelect $path $depth $index $pattern $tail $rest $kind $targets $selected)
           (case (gslt:rule:row-at $selected $targets)
             ((None LNil)
              ((Some $value)
               (let* (($nested (gslt:automata:append $path (LCons $index LNil)))
                      ($next (+ $index 1)) ($remaining (gslt:rule:scope-match-erase-at $selected $targets)) ($later (+ $selected 1)))
                 (LCons (ScopedMatcherWork $assignment
                   (LCons (ScopedMatcherTree $nested $depth $pattern $value)
                     (LCons (ScopedMatcherBag $path $depth $next $tail $rest $kind $remaining) LNil))
                   (LCons (BagChoice $nested $selected) LNil))
                   (LCons (ScopedMatcherWork $assignment
                     (LCons (ScopedMatcherBagSelect $path $depth $index $pattern $tail $rest $kind $targets $later) LNil) LNil) LNil)))))))
          ((ScopedMatcherRestCapture $path $depth $name $kind $targets)
           (let $captured (gslt:rule:scope-matcher-capture $rule $spec $ambient $site $path $depth $assignment $name
              (PCollection $kind $targets RNone))
             (gslt:rule:scope-matcher-captured-work $captured)))))))))

(: gslt:rule:scope-matcher-advance-branches (-> Atom Atom Atom %Undefined%))
(= (gslt:rule:scope-matcher-advance-branches $branches $tasks $trace)
   (case $branches
     ((LNil LNil)
      ((LCons (ScopedMatcherWork $assignment $branch-tasks $branch-trace) $rest)
       (let* (($more-tasks (gslt:automata:append $branch-tasks $tasks))
              ($more-trace (gslt:automata:append $trace $branch-trace))
              ($more (gslt:rule:scope-matcher-advance-branches $rest $tasks $trace)))
         (LCons (ScopedMatcherWork $assignment $more-tasks $more-trace) $more))))))

(: gslt:rule:scope-matcher-advance (-> Atom Atom %Undefined%))
(= (gslt:rule:scope-matcher-advance $request $work)
   (case $work
     (((ScopedMatcherWork $assignment $tasks $trace)
       (case $tasks
         ((LNil LNil)
          ((LCons $task $rest)
           (let $branches (gslt:rule:scope-matcher-expand $request $assignment $task)
             (gslt:rule:scope-matcher-advance-branches $branches $rest $trace)))))))))

(: gslt:rule:scope-matcher-tick (-> Atom Atom %Undefined%))
(= (gslt:rule:scope-matcher-tick $request $state)
   (case $state
     (((ScopedMatcherState $agenda $answers)
       (case $agenda
         ((LNil $state)
          ((LCons (ScopedMatcherWork $assignment $tasks $trace) $rest)
           (case $tasks
             ((LNil
               (let $more-answers (gslt:automata:append $answers (LCons (ScopedMatcherAnswer $assignment $trace) LNil))
                 (ScopedMatcherState $rest $more-answers)))
              ((LCons $task $tail)
               (let $branches (gslt:rule:scope-matcher-advance $request (ScopedMatcherWork $assignment $tasks $trace))
                 (let $more (gslt:automata:append $branches $rest)
                   (ScopedMatcherState $more $answers)))))))))))))

(: gslt:rule:scope-matcher-run (-> Atom Atom Atom %Undefined%))
(= (gslt:rule:scope-matcher-run $request $fuel $state)
   (if (== $fuel 0) $state
     (let $next (gslt:rule:scope-matcher-tick $request $state)
       (let $remaining (- $fuel 1)
         (gslt:rule:scope-matcher-run $request $remaining $next)))))


; The declaration-selected operation retains quote and drop provenance.
(: gslt:rule:scope-reflective-normalize (-> Atom Atom Atom %Undefined%))
(= (gslt:rule:scope-reflective-normalize $quote $drop $pattern)
   (case $pattern
     (((Var $index) $pattern)
      ((FVar $name) $pattern)
      ((PApp $head $children)
       (let $values (gslt:rule:scope-reflective-normalize-list $quote $drop $children)
         (gslt:rule:scope-reflective-normalize-finish $quote $drop $head $values)))
      ((PLam $binder $body)
       (let $value (gslt:rule:scope-reflective-normalize $quote $drop $body)
         (PLam $binder $value)))
      ((PMultiLam $arity $binders $body)
       (let $value (gslt:rule:scope-reflective-normalize $quote $drop $body)
         (PMultiLam $arity $binders $value)))
      ((PSubst $body $replacement)
       (let* (($value (gslt:rule:scope-reflective-normalize $quote $drop $body))
              ($replacement-value (gslt:rule:scope-reflective-normalize $quote $drop $replacement)))
         (PSubst $value $replacement-value)))
      ((PCollection $kind $elements $rest)
       (let $values (gslt:rule:scope-reflective-normalize-list $quote $drop $elements)
         (PCollection $kind $values $rest))))))

(: gslt:rule:scope-reflective-normalize-list (-> Atom Atom Atom %Undefined%))
(= (gslt:rule:scope-reflective-normalize-list $quote $drop $patterns)
   (case $patterns
     ((LNil LNil)
      ((LCons $pattern $rest)
       (let* (($head (gslt:rule:scope-reflective-normalize $quote $drop $pattern))
              ($tail (gslt:rule:scope-reflective-normalize-list $quote $drop $rest)))
         (LCons $head $tail))))))

(: gslt:rule:scope-reflective-normalize-finish (-> Atom Atom Atom Atom %Undefined%))
(= (gslt:rule:scope-reflective-normalize-finish $quote $drop $head $children)
   (if (== $head $quote)
     (case $children
       (((LCons (PApp $inner-head (LCons $name LNil)) LNil)
         (if (== $inner-head $drop) $name (PApp $head $children)))
        ($ordinary (PApp $head $children))))
     (PApp $head $children)))

(: gslt:rule:scope-reflective-replacement (-> Atom Atom Atom %Undefined%))
(= (gslt:rule:scope-reflective-replacement $quote $drop $replacement)
   (case $replacement
     (((PApp $head (LCons $payload LNil))
       (if (== $head $quote)
         (let $value (gslt:rule:scope-reflective-normalize $quote $drop $payload)
           (PApp $head (LCons $value LNil)))
         (gslt:rule:scope-reflective-normalize $quote $drop $replacement)))
      ($ordinary (gslt:rule:scope-reflective-normalize $quote $drop $replacement)))))

; The binder head of a normalized name: exactly the information of its
; canonical form that whole-name lookup observes. Parallel composition keeps
; only its unit, one surviving head, or opacity, so no collection is sorted.
(: gslt:rule:scope-reflective-binder-head (-> Atom Atom Atom Atom Atom %Undefined%))
(= (gslt:rule:scope-reflective-binder-head $quote $drop $parallel-kind $parallel-unit $pattern)
   (case $pattern
     (((Var $index) (BinderIndex $index))
      ((PApp $head $children)
       (let $heads (gslt:rule:scope-reflective-binder-head-list $quote $drop $parallel-kind $parallel-unit $children)
         (gslt:rule:scope-reflective-binder-head-apply $quote $drop $parallel-unit $head $heads)))
      ((PCollection $collection $elements $rest)
       (if (== $collection $parallel-kind)
         (case $rest
           ((RNone
             (let $heads (gslt:rule:scope-reflective-binder-head-list $quote $drop $parallel-kind $parallel-unit $elements)
               (gslt:rule:scope-reflective-binder-head-fold $heads)))
            ($open BinderOpaque)))
         BinderOpaque))
      ($other BinderOpaque))))

(: gslt:rule:scope-reflective-binder-head-list (-> Atom Atom Atom Atom Atom %Undefined%))
(= (gslt:rule:scope-reflective-binder-head-list $quote $drop $parallel-kind $parallel-unit $patterns)
   (case $patterns
     ((LNil LNil)
      ((LCons $pattern $rest)
       (let* (($head (gslt:rule:scope-reflective-binder-head $quote $drop $parallel-kind $parallel-unit $pattern))
              ($tail (gslt:rule:scope-reflective-binder-head-list $quote $drop $parallel-kind $parallel-unit $rest)))
         (LCons $head $tail))))))

(: gslt:rule:scope-reflective-binder-head-join (-> Atom Atom %Undefined%))
(= (gslt:rule:scope-reflective-binder-head-join $left $right)
   (case $left
     ((BinderUnit $right)
      ($present
       (case $right
         ((BinderUnit $left)
          ($other BinderOpaque)))))))

(: gslt:rule:scope-reflective-binder-head-fold (-> Atom %Undefined%))
(= (gslt:rule:scope-reflective-binder-head-fold $heads)
   (case $heads
     ((LNil BinderUnit)
      ((LCons $head $rest)
       (let $tail (gslt:rule:scope-reflective-binder-head-fold $rest)
         (gslt:rule:scope-reflective-binder-head-join $head $tail))))))

; The quote/drop equation, then the observation of a retained constructor.
(: gslt:rule:scope-reflective-binder-head-apply (-> Atom Atom Atom Atom Atom %Undefined%))
(= (gslt:rule:scope-reflective-binder-head-apply $quote $drop $parallel-unit $constructor $heads)
   (case $heads
     ((LNil (if (== $constructor $parallel-unit) BinderUnit BinderOpaque))
      ((LCons (BinderDrop $name) LNil)
       (if (== $constructor $quote)
         $name
         (if (== $constructor $drop) (BinderDrop (BinderDrop $name)) BinderOpaque)))
      ((LCons $argument LNil)
       (if (== $constructor $drop) (BinderDrop $argument) BinderOpaque))
      ($many BinderOpaque))))

; The members of the declared parallel composition: nested occurrences are
; flattened and the declared unit contributes nothing. Every other term is a
; single member.
(: gslt:rule:scope-reflective-leaves (-> Atom Atom Atom %Undefined%))
(= (gslt:rule:scope-reflective-leaves $parallel-kind $parallel-unit $pattern)
   (case $pattern
     (((PApp $head $children)
       (case $children
         ((LNil (if (== $head $parallel-unit) LNil (LCons $pattern LNil)))
          ($many (LCons $pattern LNil)))))
      ((PCollection $collection $elements $rest)
       (if (== $collection $parallel-kind)
         (case $rest
           ((RNone (gslt:rule:scope-reflective-leaves-list $parallel-kind $parallel-unit $elements))
            ($open (LCons $pattern LNil))))
         (LCons $pattern LNil)))
      ($other (LCons $pattern LNil)))))

(: gslt:rule:scope-reflective-leaves-list (-> Atom Atom Atom %Undefined%))
(= (gslt:rule:scope-reflective-leaves-list $parallel-kind $parallel-unit $patterns)
   (case $patterns
     ((LNil LNil)
      ((LCons $pattern $rest)
       (let* (($head (gslt:rule:scope-reflective-leaves $parallel-kind $parallel-unit $pattern))
              ($tail (gslt:rule:scope-reflective-leaves-list $parallel-kind $parallel-unit $rest)))
         (gslt:rule:scope-reflective-append $head $tail))))))

(: gslt:rule:scope-reflective-append (-> Atom Atom %Undefined%))
(= (gslt:rule:scope-reflective-append $left $right)
   (case $left
     ((LNil $right)
      ((LCons $item $rest)
       (let $tail (gslt:rule:scope-reflective-append $rest $right)
         (LCons $item $tail))))))

; The drop exposed by a parallel composition with exactly one member.
(: gslt:rule:scope-reflective-exposed-drop (-> Atom Atom Atom Atom %Undefined%))
(= (gslt:rule:scope-reflective-exposed-drop $drop $parallel-kind $parallel-unit $pattern)
   (let $leaves (gslt:rule:scope-reflective-leaves $parallel-kind $parallel-unit $pattern)
     (case $leaves
       (((LCons (PApp $head (LCons $name LNil)) LNil)
         (if (== $head $drop) (Some $name) None))
        ($other None)))))

; The quote/drop equation, seen through the declared parallel unit and
; nesting, at an application whose arguments are already resolved.
(: gslt:rule:scope-reflective-resolve-finish (-> Atom Atom Atom Atom Atom Atom %Undefined%))
(= (gslt:rule:scope-reflective-resolve-finish $quote $drop $parallel-kind $parallel-unit $head $children)
   (case $children
     (((LCons $payload LNil)
       (if (== $head $quote)
         (let $exposed (gslt:rule:scope-reflective-exposed-drop $drop $parallel-kind $parallel-unit $payload)
           (case $exposed
             (((Some $name) $name)
              ($none (PApp $head $children)))))
         (PApp $head $children)))
      ($other (PApp $head $children)))))

; Resolve every quotation whose payload is a drop modulo the declared parallel
; unit and nesting. Children are resolved first; no drop is executed.
(: gslt:rule:scope-reflective-resolve (-> Atom Atom Atom Atom Atom %Undefined%))
(= (gslt:rule:scope-reflective-resolve $quote $drop $parallel-kind $parallel-unit $pattern)
   (case $pattern
     (((Var $index) $pattern)
      ((FVar $name) $pattern)
      ((PApp $head $children)
       (let $values (gslt:rule:scope-reflective-resolve-list $quote $drop $parallel-kind $parallel-unit $children)
         (gslt:rule:scope-reflective-resolve-finish $quote $drop $parallel-kind $parallel-unit $head $values)))
      ((PLam $binder $body)
       (let $value (gslt:rule:scope-reflective-resolve $quote $drop $parallel-kind $parallel-unit $body)
         (PLam $binder $value)))
      ((PMultiLam $arity $binders $body)
       (let $value (gslt:rule:scope-reflective-resolve $quote $drop $parallel-kind $parallel-unit $body)
         (PMultiLam $arity $binders $value)))
      ((PSubst $body $replacement)
       (let* (($value (gslt:rule:scope-reflective-resolve $quote $drop $parallel-kind $parallel-unit $body))
              ($replacement-value (gslt:rule:scope-reflective-resolve $quote $drop $parallel-kind $parallel-unit $replacement)))
         (PSubst $value $replacement-value)))
      ((PCollection $kind $elements $rest)
       (let $values (gslt:rule:scope-reflective-resolve-list $quote $drop $parallel-kind $parallel-unit $elements)
         (PCollection $kind $values $rest))))))

(: gslt:rule:scope-reflective-resolve-list (-> Atom Atom Atom Atom Atom %Undefined%))
(= (gslt:rule:scope-reflective-resolve-list $quote $drop $parallel-kind $parallel-unit $patterns)
   (case $patterns
     ((LNil LNil)
      ((LCons $pattern $rest)
       (let* (($head (gslt:rule:scope-reflective-resolve $quote $drop $parallel-kind $parallel-unit $pattern))
              ($tail (gslt:rule:scope-reflective-resolve-list $quote $drop $parallel-kind $parallel-unit $rest)))
         (LCons $head $tail))))))

; A drop that received the selected name: a received quotation runs.
(: gslt:rule:scope-reflective-receive (-> Atom Atom Atom %Undefined%))
(= (gslt:rule:scope-reflective-receive $quote $head $name)
   (case $name
     (((PApp $inner-head (LCons $process LNil))
       (if (== $inner-head $quote) $process (PApp $head (LCons $name LNil))))
      ($ordinary (PApp $head (LCons $name LNil))))))

; Substitute structurally in a resolved term. At a genuine quotation, `Opaque`
; keeps it as written and `(Enter $value)` substitutes inside it with `$value` as
; the selected binder's value. A drop whose whole name is the selected binder
; receives the replacement; every other drop is substituted through. Ordinary
; indices are lowered.
(: gslt:rule:scope-reflective-substitute-at (-> Atom Atom Atom Atom Atom Atom Atom Atom %Undefined%))
(= (gslt:rule:scope-reflective-substitute-at $quote $drop $parallel-kind $parallel-unit $inside $depth $replacement $pattern)
   (case $pattern
     (((Var $index) (gslt:rule:instantiate-bvar-at $depth $replacement $pattern))
      ((FVar $name) $pattern)
      ((PApp $head $children)
       (gslt:rule:scope-reflective-substitute-apply $quote $drop $parallel-kind $parallel-unit $inside $depth $replacement $head $children))
      ((PLam $binder $body)
       (let* (($next (+ $depth 1))
              ($value (gslt:rule:scope-reflective-substitute-at $quote $drop $parallel-kind $parallel-unit $inside $next $replacement $body)))
         (PLam $binder $value)))
      ((PMultiLam $arity $binders $body)
       (let* (($next (+ $depth $arity))
              ($value (gslt:rule:scope-reflective-substitute-at $quote $drop $parallel-kind $parallel-unit $inside $next $replacement $body)))
         (PMultiLam $arity $binders $value)))
      ((PSubst $body $nested-replacement)
       (let* (($next (+ $depth 1))
              ($value (gslt:rule:scope-reflective-substitute-at $quote $drop $parallel-kind $parallel-unit $inside $next $replacement $body))
              ($replacement-value (gslt:rule:scope-reflective-substitute-at $quote $drop $parallel-kind $parallel-unit $inside $depth $replacement $nested-replacement)))
         (PSubst $value $replacement-value)))
      ((PCollection $kind $elements $rest)
       (let $values (gslt:rule:scope-reflective-substitute-list-at $quote $drop $parallel-kind $parallel-unit $inside $depth $replacement $elements)
         (PCollection $kind $values $rest))))))

(: gslt:rule:scope-reflective-substitute-list-at (-> Atom Atom Atom Atom Atom Atom Atom Atom %Undefined%))
(= (gslt:rule:scope-reflective-substitute-list-at $quote $drop $parallel-kind $parallel-unit $inside $depth $replacement $patterns)
   (case $patterns
     ((LNil LNil)
      ((LCons $pattern $rest)
       (let* (($head (gslt:rule:scope-reflective-substitute-at $quote $drop $parallel-kind $parallel-unit $inside $depth $replacement $pattern))
              ($tail (gslt:rule:scope-reflective-substitute-list-at $quote $drop $parallel-kind $parallel-unit $inside $depth $replacement $rest)))
         (LCons $head $tail))))))

(: gslt:rule:scope-reflective-substitute-apply (-> Atom Atom Atom Atom Atom Atom Atom Atom Atom %Undefined%))
(= (gslt:rule:scope-reflective-substitute-apply $quote $drop $parallel-kind $parallel-unit $inside $depth $replacement $head $children)
   (case $children
     (((LCons $payload LNil)
       (gslt:rule:scope-reflective-substitute-unary $quote $drop $parallel-kind $parallel-unit $inside $depth $replacement $head $payload))
      ($many
       (let $values (gslt:rule:scope-reflective-substitute-list-at $quote $drop $parallel-kind $parallel-unit $inside $depth $replacement $children)
         (PApp $head $values))))))

(: gslt:rule:scope-reflective-substitute-unary (-> Atom Atom Atom Atom Atom Atom Atom Atom Atom %Undefined%))
(= (gslt:rule:scope-reflective-substitute-unary $quote $drop $parallel-kind $parallel-unit $inside $depth $replacement $head $payload)
   (if (== $head $quote)
     (case $inside
       ((Opaque (PApp $head (LCons $payload LNil)))
        ((Enter $value)
         (let $entered (gslt:rule:scope-reflective-substitute-at $quote $drop $parallel-kind $parallel-unit $inside $depth $value $payload)
           (PApp $head (LCons $entered LNil))))))
     (if (== $head $drop)
       (let $binder (gslt:rule:scope-reflective-binder-head $quote $drop $parallel-kind $parallel-unit $payload)
         (case $binder
           (((BinderIndex $level)
             (if (== $level $depth)
               (let $value (gslt:rule:instantiate-bvar-at $depth $replacement (Var $depth))
                 (gslt:rule:scope-reflective-receive $quote $head $value))
               (let $value (gslt:rule:scope-reflective-substitute-at $quote $drop $parallel-kind $parallel-unit $inside $depth $replacement $payload)
                 (PApp $head (LCons $value LNil)))))
            ($other
             (let $value (gslt:rule:scope-reflective-substitute-at $quote $drop $parallel-kind $parallel-unit $inside $depth $replacement $payload)
               (PApp $head (LCons $value LNil)))))))
       (let $value (gslt:rule:scope-reflective-substitute-at $quote $drop $parallel-kind $parallel-unit $inside $depth $replacement $payload)
         (PApp $head (LCons $value LNil))))))

; Normalize the replacement, resolve the body's quotations of drops, then
; substitute structurally. The declared quote scope decides a genuine quotation:
; a closed scope keeps it opaque; a reaching scope enters it, with the
; replacement (apply view), the frozen spelling (freeze view), or the replacement
; under the context constructor (closure view) as the selected binder's value.
(: gslt:rule:scope-reflective-binder-operation (-> Atom Atom Atom %Undefined%))
(= (gslt:rule:scope-reflective-binder-operation $declaration $replacement $body)
   (case $declaration
     (((ReflectivePresentation $name $process-sort $name-sort $quote $drop $parallel-kind $parallel-unit $quote-drop-equation $scope)
       (let* (($normalized (gslt:rule:scope-reflective-replacement $quote $drop $replacement))
              ($resolved (gslt:rule:scope-reflective-resolve $quote $drop $parallel-kind $parallel-unit $body))
              ($inside (case $scope
                         ((QuoteClosed Opaque)
                          ((QuoteReaching QuoteApply) (Enter $normalized))
                          ((QuoteReaching (QuoteFreeze $spelling)) (Enter $spelling))
                          ((QuoteReaching (QuoteClosure $context)) (Enter (PApp $context (LCons $normalized LNil)))))))
              ($value (gslt:rule:scope-reflective-substitute-at $quote $drop $parallel-kind $parallel-unit $inside 0 $normalized $resolved)))
         (Some $value)))
      ($invalid None))))


; Scoped RHS traversal uses the original authored site, path and depth.
; The optional declaration selects the original reflective substitution operation.
(: gslt:rule:scope-binder-operation (-> Atom Atom Atom %Undefined%))
(= (gslt:rule:scope-binder-operation $operation $replacement $body)
   (case $operation
     ((None
       (let $result (gslt:rule:instantiate-bvar-at 0 $replacement $body)
         (Some $result)))
      ((Some $declaration)
       (gslt:rule:scope-reflective-binder-operation $declaration $replacement $body))
      ($invalid None))))

(: gslt:rule:scope-instantiate-slot (-> Atom Atom Atom Atom Atom Atom Atom Atom %Undefined%))
(= (gslt:rule:scope-instantiate-slot $rule $spec $ambient $site $path $depth $assignment $name)
   (case (gslt:automata:binding $name $assignment)
     (((Some $value)
       (case (gslt:rule:scope-metadata-arguments $rule $spec $name $site $path)
         (((Some $arguments)
           (gslt:rule:scope-instantiate-value $value $ambient $depth $arguments))
          ($missing None))))
      ($missing None))))

(: gslt:rule:scope-instantiate-at (-> Atom Atom Atom Atom Atom Atom Atom Atom Atom %Undefined%))
(= (gslt:rule:scope-instantiate-at $operation $rule $spec $ambient $site $path $depth $assignment $pattern)
   (case $pattern
     (((FVar $name)
       (gslt:rule:scope-instantiate-slot $rule $spec $ambient $site $path $depth $assignment $name))
      ((Var $index) (Some $pattern))
      ((PApp $head $children)
       (case (gslt:rule:scope-instantiate-args-at $operation $rule $spec $ambient $site $path $depth $assignment 0 $children)
         (((Some $values) (let $result (PApp $head $values) (Some $result)))
          ($failed None))))
      ((PLam $binder $body)
       (let* (($child-path (gslt:automata:append $path (LCons 0 LNil)))
              ($child-depth (+ $depth 1)))
         (case (gslt:rule:scope-instantiate-at $operation $rule $spec $ambient $site $child-path $child-depth $assignment $body)
           (((Some $value) (let $result (PLam $binder $value) (Some $result)))
            ($failed None)))))
      ((PMultiLam $arity $binders $body)
       (let* (($child-path (gslt:automata:append $path (LCons 0 LNil)))
              ($child-depth (+ $depth $arity)))
         (case (gslt:rule:scope-instantiate-at $operation $rule $spec $ambient $site $child-path $child-depth $assignment $body)
           (((Some $value) (let $result (PMultiLam $arity $binders $value) (Some $result)))
            ($failed None)))))
      ((PSubst $body $replacement)
       (let* (($body-path (gslt:automata:append $path (LCons 0 LNil)))
              ($body-depth (+ $depth 1)))
         (case (gslt:rule:scope-instantiate-at $operation $rule $spec $ambient $site $body-path $body-depth $assignment $body)
           (((Some $body-value)
             (let $replacement-path (gslt:automata:append $path (LCons 1 LNil))
               (case (gslt:rule:scope-instantiate-at $operation $rule $spec $ambient $site $replacement-path $depth $assignment $replacement)
                 (((Some $replacement-value)
                   (gslt:rule:scope-binder-operation $operation $replacement-value $body-value))
                  ($failed None)))))
            ($failed None)))))
      ((PCollection $kind $elements $rest)
       (case (gslt:rule:scope-instantiate-args-at $operation $rule $spec $ambient $site $path $depth $assignment 0 $elements)
         (((Some $explicit)
           (case $rest
             ((RNone (let $result (PCollection $kind $explicit RNone) (Some $result)))
              ((RSome $name)
               (let* (($length (gslt:automata:length $elements))
                      ($rest-path (gslt:automata:append $path (LCons $length LNil))))
                 (case (gslt:rule:scope-instantiate-slot $rule $spec $ambient $site $rest-path $depth $assignment $name)
                   (((Some (PCollection $actual-kind $residual RNone))
                     (if (== $actual-kind $kind)
                       (let* (($values (gslt:automata:append $explicit $residual))
                              ($result (PCollection $kind $values RNone)))
                         (Some $result)) None))
                    ($failed None)))))
              ($invalid None))))
          ($failed None))))
      ($invalid None))))

(: gslt:rule:scope-instantiate-args-at (-> Atom Atom Atom Atom Atom Atom Atom Atom Atom Atom %Undefined%))
(= (gslt:rule:scope-instantiate-args-at $operation $rule $spec $ambient $site $path $depth $assignment $index $patterns)
   (case $patterns
     ((LNil (Some LNil))
      ((LCons $pattern $rest)
       (let $child-path (gslt:automata:append $path (LCons $index LNil))
         (case (gslt:rule:scope-instantiate-at $operation $rule $spec $ambient $site $child-path $depth $assignment $pattern)
           (((Some $head)
             (let $next (+ $index 1)
               (case (gslt:rule:scope-instantiate-args-at $operation $rule $spec $ambient $site $path $depth $assignment $next $rest)
                 (((Some $tail) (let $values (LCons $head $tail) (Some $values)))
                  ($failed None)))))
            ($failed None)))))
      ($invalid None))))

(: gslt:rule:scope-reduct (-> Atom Atom Atom Atom Atom %Undefined%))
(= (gslt:rule:scope-reduct $operation $rule $spec $ambient $assignment)
   (case $rule
     (((ScopedRewriteRuleV1 $name $context $premises $left $right $bindings)
       (gslt:rule:scope-instantiate-at $operation $rule $spec $ambient RuleRight LNil 0 $assignment $right))
      ($invalid None))))


; Original premise frames retain suspended matcher states and complete receipts.
(: gslt:premise:root-match-expand-in (-> Atom Atom %Undefined%))
(= (gslt:premise:root-match-expand-in $snapshot $task)
   (case $snapshot
     (((PremiseEnvironment $declarations $rewrites $specifications $provider $reflection $free)
       (case $task
         (((PremiseRootMatch $bound $type $source $index $rule $spec $matcher $cursor $tail)
           (case $rule
             (((ScopedRewriteRuleV1 $name $types $premises $left $right $bindings)
               (case $matcher
                 (((ScopedMatcherState $agenda $answers)
                   (case (gslt:rule:row-at $cursor $answers)
                     (((Some (ScopedMatcherAnswer $assignment $trace))
                       (let $next (+ $cursor 1)
                         (let $later (PremiseRootMatch $bound $type $source $index $rule $spec $matcher $next $tail)
                           (if (gslt:premise:check-assignment $declarations $free $bound $rule $spec $assignment)
                             (Some (PremiseExpansion
                               (LCons (PremiseEvaluate
                                 (PremisesGoal (PremiseContext $index $rule $spec $bound 0 0) $premises $assignment)
                                 (PremiseRootBody $bound $type $source $index $rule $spec $trace $assignment $tail))
                                 (LCons $later LNil)) LNil LNil))
                             (Some (PremiseExpansion (LCons $later LNil) LNil LNil))))))
                      (None
                       (if (gslt:rule:scope-matcher-complete $matcher)
                         (Some (PremiseExpansion LNil LNil LNil))
                         (let $ambient (gslt:automata:length $bound)
                           (let $request (ScopedMatcherRequest $rule $spec $ambient RuleLeft LNil 0 LNil $left $source)
                             (let $advanced (gslt:rule:scope-matcher-tick $request $matcher)
                               (Some (PremiseExpansion
                                 (LCons (PremiseRootMatch $bound $type $source $index $rule $spec $advanced $cursor $tail) LNil)
                                 LNil LNil)))))))
                      ($badAnswer None))))
                  ($badMatcher None))))
              ($badRule None))))
          ($badTask None))))
      ($badEnvironment None))))

(: gslt:premise:target-match-expand-in (-> Atom Atom %Undefined%))
(= (gslt:premise:target-match-expand-in $snapshot $task)
   (case $snapshot
     (((PremiseEnvironment $declarations $rewrites $specifications $provider $reflection $free)
       (case $task
         (((PremiseTargetMatch $call $index $trace $captured $completed $history $target $matcher $cursor $tail)
           (case $call
             (((PremiseStepCall $context $premise $initial $binders $type $source $target-schema)
               (case $context
                 (((PremiseContext $rule-index $rule $spec $bound $premise-index $quantifiers)
                   (case $matcher
                     (((ScopedMatcherState $agenda $answers)
                       (case (gslt:rule:row-at $cursor $answers)
                         (((Some (ScopedMatcherAnswer $assignment $target-trace))
                           (let $next (+ $cursor 1)
                             (let $later (PremiseTargetMatch $call $index $trace $captured $completed $history $target $matcher $next $tail)
                               (if (gslt:premise:check-assignment $declarations $free $bound $rule $spec $assignment)
                                 (let $child-bound (gslt:automata:append $binders $bound)
                                   (Some (PremiseExpansion
                                     (LCons (PremiseDeliver
                                       (PremiseResult (PremiseGoal $context $premise $initial)
                                         (PremiseAnswer $assignment
                                           (PremiseChildEvent $premise-index $quantifiers $index $child-bound $source $target
                                             $trace $target-trace $captured $completed $history))) $tail)
                                       (LCons $later LNil)) LNil LNil)))
                                 (Some (PremiseExpansion (LCons $later LNil) LNil LNil))))))
                          (None
                           (if (gslt:rule:scope-matcher-complete $matcher)
                             (Some (PremiseExpansion LNil LNil LNil))
                             (let* (($ambient (gslt:automata:length $bound))
                                    ($depth (gslt:automata:length $binders))
                                    ($request (ScopedMatcherRequest $rule $spec $ambient
                                      (RulePremise $premise-index $quantifiers 1) LNil $depth $initial $target-schema $target))
                                    ($advanced (gslt:rule:scope-matcher-tick $request $matcher)))
                               (Some (PremiseExpansion
                                 (LCons (PremiseTargetMatch $call $index $trace $captured $completed $history $target $advanced $cursor $tail) LNil)
                                 LNil LNil)))))
                          ($badAnswer None))))
                      ($badMatcher None))))
                  ($badContext None))))
              ($badCall None))))
          ($badTask None))))
      ($badEnvironment None))))

(: gslt:premise:root-body-deliver-in (-> Atom Atom Atom %Undefined%))
(= (gslt:premise:root-body-deliver-in $snapshot $result $continuation)
   (case $snapshot
     (((PremiseEnvironment $declarations $rewrites $specifications $provider $reflection $free)
       (case $continuation
         (((PremiseRootBody $bound $type $source $index $rule $spec $trace $captured $tail)
           (case $result
             (((PremiseResult $goal (PremisesAnswer $completed $history))
               (let* (($operation (gslt:premise:substitution-presentation $reflection $rule))
                      ($ambient (gslt:automata:length $bound)))
                 (case (gslt:rule:scope-reduct $operation $rule $spec $ambient $completed)
                   ((None (Some (PremiseExpansion LNil LNil (LCons (PremiseTargetProjection $index) LNil))))
                    ((Some $target)
                     (if (gslt:premise:open-well-sorted $declarations $free $bound $type $target)
                       (Some (PremiseExpansion
                         (LCons (PremiseDeliver
                           (PremiseResult (RootGoal $bound $type $source $index)
                             (RootAnswer $trace $captured $completed $history $target)) $tail) LNil)
                         LNil LNil))
                       (Some (PremiseExpansion LNil LNil LNil))))
                    ($badTarget None)))))
              ($badResult None))))
          ($badContinuation None))))
      ($badEnvironment None))))

(: gslt:premise:stepped-deliver-in (-> Atom Atom Atom %Undefined%))
(= (gslt:premise:stepped-deliver-in $snapshot $result $continuation)
   (case $snapshot
     (((PremiseEnvironment $declarations $rewrites $specifications $provider $reflection $free)
       (case $continuation
         (((PremiseStepped $call $tail)
           (case $call
             (((PremiseStepCall $context $premise $initial $binders $type $source $target-schema)
               (case $context
                 (((PremiseContext $rule-index $rule $spec $bound $premise-index $quantifiers)
                   (case $result
                     (((PremiseResult $goal (StepsAnswer $index $trace $captured $completed $history $target))
                       (let* (($ambient (gslt:automata:length $bound))
                              ($depth (gslt:automata:length $binders))
                              ($request (ScopedMatcherRequest $rule $spec $ambient
                                (RulePremise $premise-index $quantifiers 1) LNil $depth $initial $target-schema $target))
                              ($matcher (gslt:rule:scope-matcher-start $request)))
                         (Some (PremiseExpansion
                           (LCons (PremiseTargetMatch $call $index $trace $captured $completed $history $target $matcher 0 $tail) LNil)
                           LNil LNil))))
                      ($badResult None))))
                  ($badContext None))))
              ($badCall None))))
          ($badContinuation None))))
      ($badEnvironment None))))


; The original premise scheduler commits one already-expanded work frame.
; Work, answers and unresolved obligations keep their authored order.
(: gslt:premise:machine-commit (-> Atom Atom %Undefined%))
(= (gslt:premise:machine-commit $state $expanded)
   (case $state
     (((PremiseState LNil $answers $unresolved $work) (Some $state))
      ((PremiseState (LCons $task $rest) $answers $unresolved $work)
       (case $expanded
         (((Some (PremiseExpansion $tasks $new-answers $new-unresolved))
           (let* (($agenda (gslt:automata:append $tasks $rest))
                  ($all-answers (gslt:automata:append $answers $new-answers))
                  ($all-unresolved (gslt:automata:append $unresolved $new-unresolved))
                  ($next-work (+ $work 1)))
             (Some (PremiseState $agenda $all-answers $all-unresolved $next-work))))
          ($pending None))))
      ($bad None))))

; Settled work with outstanding obligations has not completed.
(: gslt:premise:machine-complete (-> Atom %Undefined%))
(= (gslt:premise:machine-complete $state)
   (case $state
     (((PremiseState LNil $answers LNil $work) True)
      ($pending False))))


; Retained scheduling for the original conditional-premise task machine.
; Expansion keeps its source-owned task and continuation representation.
(: gslt:premise:machine-start (-> Atom %Undefined%))
(= (gslt:premise:machine-start $goal)
   (Some (PremiseState
     (LCons (PremiseEvaluate $goal (PremiseDone $goal)) LNil)
     LNil LNil 0)))

(: gslt:premise:machine-tick (-> Atom Atom %Undefined%))
(= (gslt:premise:machine-tick $environment $state)
   (case $state
     (((PremiseState LNil $answers $unresolved $work) (Some $state))
      ((PremiseState (LCons $task $rest) $answers $unresolved $work)
       (let $expanded (gslt:premise:machine-expand-in $environment $task)
         (gslt:premise:machine-commit $state $expanded)))
      ($bad None))))

(: gslt:premise:machine-run (-> Atom Atom Atom %Undefined%))
(= (gslt:premise:machine-run $environment $fuel $state)
   (if (== $fuel 0)
     (Some $state)
     (let $next (gslt:premise:machine-tick $environment $state)
       (case $next
         (((Some $next-state)
           (let $remaining (- $fuel 1)
             (gslt:premise:machine-run $environment $remaining $next-state)))
          ($unavailable None))))))
; Check the complete authored binding declaration before a root search starts.
(: gslt:premise:admission-keys (-> Atom %Undefined%))
(= (gslt:premise:admission-keys $rows)
   (case $rows
     ((LNil LNil)
      ((LCons (TypeBinding $name $type) $rest)
       (let $keys (gslt:premise:admission-keys $rest) (LCons $name $keys)))
      ((LCons (RuleDependency $name $types) $rest)
       (let $keys (gslt:premise:admission-keys $rest) (LCons $name $keys)))
      ($bad None))))

(: gslt:premise:admission-occurrence-keys (-> Atom %Undefined%))
(= (gslt:premise:admission-occurrence-keys $rows)
   (case $rows
     ((LNil LNil)
      ((LCons (RuleOccurrence $name $site $path $arguments) $rest)
       (let $keys (gslt:premise:admission-occurrence-keys $rest)
         (LCons (RuleOccurrence $name $site $path LNil) $keys)))
      ($bad None))))

(: gslt:premise:admission-nodup (-> Atom %Undefined%))
(= (gslt:premise:admission-nodup $keys)
   (case $keys
     ((LNil True)
      ((LCons $key $rest)
       (if (gslt:automata:member $key $rest) False
         (gslt:premise:admission-nodup $rest)))
      ($bad False))))

(: gslt:premise:admission-context-covered (-> Atom Atom %Undefined%))
(= (gslt:premise:admission-context-covered $context $dependencies)
   (case $context
     ((LNil True)
      ((LCons $name $rest)
       (if (gslt:automata:member $name $dependencies)
         (gslt:premise:admission-context-covered $rest $dependencies) False))
      ($bad False))))

(: gslt:premise:admission-occurrences (-> Atom Atom Atom %Undefined%))
(= (gslt:premise:admission-occurrences $rule $spec $rows)
   (case $rows
     ((LNil True)
      ((LCons (RuleOccurrence $name $site $path $arguments) $rest)
       (if (gslt:rule:scope-metadata-occurrence-declared $rule
             (RuleOccurrence $name $site $path $arguments))
         (case (gslt:rule:scope-metadata-dependencies $spec $name)
           (((Some $dependencies)
             (case (gslt:rule:scope-metadata-occurrence-depth-at-site $rule $site $path)
               (((Some $depth)
                 (let* (($arity (gslt:automata:length $arguments))
                        ($expected (gslt:automata:length $dependencies)))
                   (if (== $arity $expected)
                     (if (gslt:premise:ground-list-at $depth $arguments)
                       (gslt:premise:admission-occurrences $rule $spec $rest) False)
                     False)))
                ($missingDepth False))))
            ($missingDependencies False)))
         False))
      ($bad False))))

(: gslt:premise:binding-admitted (-> Atom Atom %Undefined%))
(= (gslt:premise:binding-admitted $rule $spec)
   (case $rule
     (((ScopedRewriteRuleV1 $label $context $premises $left $right $bindings)
       (case $spec
         (((RuleBindingSpec $dependencies $occurrences)
           (let* (($contextKeys (gslt:premise:admission-keys $context))
                  ($dependencyKeys (gslt:premise:admission-keys $dependencies))
                  ($occurrenceKeys (gslt:premise:admission-occurrence-keys $occurrences)))
             (if (gslt:premise:admission-nodup $contextKeys)
               (if (gslt:premise:admission-nodup $dependencyKeys)
                 (if (gslt:premise:admission-nodup $occurrenceKeys)
                   (let* (($contextCount (gslt:automata:length $context))
                          ($dependencyCount (gslt:automata:length $dependencies)))
                     (if (== $contextCount $dependencyCount)
                       (if (gslt:premise:admission-context-covered $contextKeys $dependencyKeys)
                         (gslt:premise:admission-occurrences $rule $spec $occurrences) False)
                       False))
                   False)
                 False)
               False)))
          ($badSpec False))))
      ($badRule False))))
; Environment transitions retain the original scheduler, goals, tasks and continuation wires.

(: gslt:premise:query-obligations (-> Atom %Undefined%))
(=
  (gslt:premise:query-obligations $reasons)
  (case
    $reasons
    ((LNil LNil)
      ((LCons $reason $rest)
        (let
          $tail
          (gslt:premise:query-obligations $rest)
          (LCons (PremiseQueryObligation $reason) $tail)))
      ($badReasons None))))

(: gslt:premise:machine-deliver-in (-> Atom Atom Atom %Undefined%))
(=
  (gslt:premise:machine-deliver-in $environment $result $continuation)
  (case
    $continuation
    (((PremiseRootBody $bound $type $source $index $rule $spec $trace $captured $tail)
       (gslt:premise:root-body-deliver-in $environment $result $continuation))
      ((PremiseStepped $call $tail)
        (gslt:premise:stepped-deliver-in $environment $result $continuation))
      ($administrative (gslt:premise:machine-deliver $result $continuation)))))

(: gslt:premise:machine-evaluate-in (-> Atom Atom Atom %Undefined%))
(=
  (gslt:premise:machine-evaluate-in $environment $goal $continuation)
  (case
    $environment
    (((PremiseEnvironment
        $declarations
        $rewrites
        $specifications
        (PremiseProvider $signatures $rows)
        $reflection
        $free)
       (case
         $goal
         (((PremiseGoal $context $premise $initial)
            (case
              $context
              (((PremiseContext $ruleIndex $rule $spec $bound $premiseIndex $quantifiers)
                 (case
                   $premise
                   (((RelationQuery $relation $arguments)
                      (let
                        $request
                        (PremiseQueryRequest $context $relation $arguments $initial)
                        (Some
                          (PremiseExpansion
                            (LCons
                              (PremiseQuery
                                $request
                                (PremiseState (LCons PremiseQueryStart LNil) LNil LNil 0)
                                0
                                $continuation)
                              LNil)
                            LNil
                            LNil))))
                     ((Freshness $name $subjectSchema)
                       (let
                         $ambient
                         (gslt:automata:length $bound)
                         (let
                           $nameOption
                           (case
                             (gslt:automata:binding $name $initial)
                             ((None (Some $name))
                               ((Some $stored)
                                 (case
                                   (gslt:rule:scope-instantiate-value $stored $ambient 0 LNil)
                                   (((Some (FVar $atom)) (Some $atom)) ($nonName None))))
                               ($badLookup None)))
                           (case
                             $nameOption
                             ((None
                                (Some
                                  (PremiseExpansion
                                    LNil
                                    LNil
                                    (LCons (PremiseFreshnessProjection $premiseIndex $quantifiers) LNil))))
                               ((Some $atom)
                                 (case
                                   (gslt:rule:scope-instantiate-at
                                     None
                                     $rule
                                     $spec
                                     $ambient
                                     (RulePremise $premiseIndex $quantifiers 0)
                                     LNil
                                     0
                                     $initial
                                     $subjectSchema)
                                   ((None
                                      (Some
                                        (PremiseExpansion
                                          LNil
                                          LNil
                                          (LCons
                                            (PremiseFreshnessProjection $premiseIndex $quantifiers)
                                            LNil))))
                                     ((Some $subject)
                                       (if
                                         (gslt:premise:fresh $atom $subject)
                                         (Some
                                           (PremiseExpansion
                                             (LCons
                                               (PremiseDeliver
                                                 (PremiseResult
                                                   $goal
                                                   (PremiseAnswer
                                                     $initial
                                                     (PremiseFreshnessEvent
                                                       $premiseIndex
                                                       $quantifiers
                                                       $atom
                                                       $subject)))
                                                 $continuation)
                                               LNil)
                                             LNil
                                             LNil))
                                         (Some (PremiseExpansion LNil LNil LNil))))
                                     ($badSubject None))))
                               ($badName None))))))
                     ((ForAll $collection $parameter $body)
                       (gslt:premise:machine-evaluate $declarations $free $goal $continuation))
                     ((Congruence $sourceSchema $targetSchema)
                       (case
                         (gslt:premise:source-type $declarations $rule $sourceSchema)
                         ((None
                            (Some
                              (PremiseExpansion
                                LNil
                                LNil
                                (LCons (PremiseStepSort $premiseIndex $quantifiers) LNil))))
                           ((Some $type)
                             (let
                               $ambient
                               (gslt:automata:length $bound)
                               (case
                                 (gslt:rule:scope-instantiate-at
                                   None
                                   $rule
                                   $spec
                                   $ambient
                                   (RulePremise $premiseIndex $quantifiers 0)
                                   LNil
                                   0
                                   $initial
                                   $sourceSchema)
                                 ((None
                                    (Some
                                      (PremiseExpansion
                                        LNil
                                        LNil
                                        (LCons (PremiseStepProjection $premiseIndex $quantifiers) LNil))))
                                   ((Some $actualSource)
                                     (Some
                                       (PremiseExpansion
                                         (LCons
                                           (PremiseEvaluate
                                             (StepsGoal $bound $type $actualSource $ruleIndex)
                                             (PremiseStepped
                                               (PremiseStepCall
                                                 $context
                                                 $premise
                                                 $initial
                                                 LNil
                                                 $type
                                                 $actualSource
                                                 $targetSchema)
                                               $continuation))
                                           LNil)
                                         LNil
                                         LNil)))
                                   ($badProjection None)))))
                           ($badType None))))
                     ((ScopedStep $binders $type $sourceSchema $targetSchema)
                       (let*
                         (($ambient (gslt:automata:length $bound))
                           ($depth (gslt:automata:length $binders))
                           ($effectiveBound (gslt:automata:append $binders $bound)))
                         (case
                           (gslt:rule:scope-instantiate-at
                             None
                             $rule
                             $spec
                             $ambient
                             (RulePremise $premiseIndex $quantifiers 0)
                             LNil
                             $depth
                             $initial
                             $sourceSchema)
                           ((None
                              (Some
                                (PremiseExpansion
                                  LNil
                                  LNil
                                  (LCons (PremiseStepProjection $premiseIndex $quantifiers) LNil))))
                             ((Some $actualSource)
                               (Some
                                 (PremiseExpansion
                                   (LCons
                                     (PremiseEvaluate
                                       (StepsGoal $effectiveBound $type $actualSource $ruleIndex)
                                       (PremiseStepped
                                         (PremiseStepCall
                                           $context
                                           $premise
                                           $initial
                                           $binders
                                           $type
                                           $actualSource
                                           $targetSchema)
                                         $continuation))
                                     LNil)
                                   LNil
                                   LNil)))
                             ($badProjection None)))))
                     ($badPremise None))))
                ($badContext None))))
           ((RootGoal $bound $type $source $index)
             (case
               (gslt:rule:row-at $index $rewrites)
               ((None (Some (PremiseExpansion LNil LNil (LCons (PremiseRuleUnavailable $index) LNil))))
                 ((Some $rule)
                   (case
                     $rule
                     (((ScopedRewriteRuleV1 $ruleName $ruleTypes $premises $left $right $bindings)
                        (case
                          (gslt:premise:specification $index $specifications)
                          ((None
                             (Some
                               (PremiseExpansion
                                 LNil
                                 LNil
                                 (LCons (PremiseBindingUnavailable $index) LNil))))
                            ((Some $spec)
                              (if
                                (gslt:premise:binding-admitted $rule $spec)
                                (if
                                  (gslt:premise:open-well-sorted
                                    $declarations
                                    $free
                                    $bound
                                    $type
                                    $source)
                                  (let*
                                    (($ambient (gslt:automata:length $bound))
                                      ($query
                                        (ScopedMatcherRequest
                                          $rule
                                          $spec
                                          $ambient
                                          RuleLeft
                                          LNil
                                          0
                                          LNil
                                          $left
                                          $source))
                                      ($matcher (gslt:rule:scope-matcher-start $query)))
                                    (Some
                                      (PremiseExpansion
                                        (LCons
                                          (PremiseRootMatch
                                            $bound
                                            $type
                                            $source
                                            $index
                                            $rule
                                            $spec
                                            $matcher
                                            0
                                            $continuation)
                                          LNil)
                                        LNil
                                        LNil)))
                                  (Some
                                    (PremiseExpansion
                                      LNil
                                      LNil
                                      (LCons (PremiseSourceRejected $index) LNil))))
                                (Some
                                  (PremiseExpansion
                                    LNil
                                    LNil
                                    (LCons (PremiseBindingRejected $index) LNil)))))
                            ($badSpec None))))
                       ($badRule None))))
                 ($badLookup None))))
           ((PremisesGoal $context $premises $initial)
             (gslt:premise:machine-evaluate $declarations $free $goal $continuation))
           ((QuantifiedGoal $context $parameter $body $index $elements $initial)
             (gslt:premise:machine-evaluate $declarations $free $goal $continuation))
           ((StepsGoal $bound $type $source $limit)
             (gslt:premise:machine-evaluate $declarations $free $goal $continuation))
           ($badGoal None))))
      ($badEnvironment None))))

(: gslt:premise:machine-expand-in (-> Atom Atom %Undefined%))
(=
  (gslt:premise:machine-expand-in $environment $task)
  (case
    $environment
    (((PremiseEnvironment
        $declarations
        $rewrites
        $specifications
        (PremiseProvider $signatures $rows)
        $reflection
        $free)
       (case
         $task
         (((PremiseEvaluate $goal $continuation)
            (gslt:premise:machine-evaluate-in $environment $goal $continuation))
           ((PremiseDeliver $result $continuation)
             (gslt:premise:machine-deliver-in $environment $result $continuation))
           ((PremiseQuery $request $queryState $cursor $continuation)
             (case
               $request
               (((PremiseQueryRequest $context $relation $arguments $initial)
                  (case
                    $context
                    (((PremiseContext $ruleIndex $rule $spec $bound $premiseIndex $quantifiers)
                       (case
                         $queryState
                         (((PremiseState $agenda $answers $unresolved $work)
                            (case
                              (gslt:rule:row-at $cursor $answers)
                              (((Some (PremiseQueryAnswer $rowIndex $assignment $origins))
                                 (let
                                   $next
                                   (+ $cursor 1)
                                   (Some
                                     (PremiseExpansion
                                       (LCons
                                         (PremiseDeliver
                                           (PremiseResult
                                             (PremiseGoal
                                               $context
                                               (RelationQuery $relation $arguments)
                                               $initial)
                                             (PremiseAnswer
                                               $assignment
                                               (PremiseQueryEvent
                                                 $premiseIndex
                                                 $quantifiers
                                                 $rowIndex
                                                 $origins)))
                                           $continuation)
                                         (LCons
                                           (PremiseQuery $request $queryState $next $continuation)
                                           LNil))
                                       LNil
                                       LNil))))
                                (None
                                  (case
                                    $agenda
                                    ((LNil
                                       (let
                                         $reasons
                                         (gslt:premise:query-obligations $unresolved)
                                         (Some (PremiseExpansion LNil LNil $reasons))))
                                      ((LCons $queryTask $queryRest)
                                        (let
                                          $expanded
                                          (gslt:premise:query-expand-in
                                            $environment
                                            $request
                                            $queryTask)
                                          (case
                                            (gslt:premise:machine-commit $queryState $expanded)
                                            (((Some $nextState)
                                               (Some
                                                 (PremiseExpansion
                                                   (LCons
                                                     (PremiseQuery
                                                       $request
                                                       $nextState
                                                       $cursor
                                                       $continuation)
                                                     LNil)
                                                   LNil
                                                   LNil)))
                                              ($badCommit None)))))
                                      ($badAgenda None))))
                                ($badAnswer None))))
                           ($badState None))))
                      ($badContext None))))
                 ($badRequest None))))
           ((PremiseRootMatch $bound $type $source $index $rule $spec $matcher $cursor $continuation)
             (gslt:premise:root-match-expand-in $environment $task))
           ((PremiseTargetMatch
              $call
              $index
              $trace
              $captured
              $completed
              $history
              $target
              $matcher
              $cursor
              $continuation)
             (gslt:premise:target-match-expand-in $environment $task))
           ((PremiseScanChildren $bound $type $source $limit $cursor $continuation)
             (gslt:premise:machine-expand $declarations $free $task))
           ($badTask None))))
      ($badEnvironment None))))

(: gslt:rule:site-replacement-represented (-> Atom Atom Atom Atom %Undefined%))
(= (gslt:rule:site-replacement-represented $declarations $context $frames $target)
   (case (ReplacementShape $context $frames)
     (((ReplacementShape ContextHole LNil) True)
      ((ReplacementShape (ContextApp $head $before $inner $after)
                         (LCons (TypingApplication $declaration $index) $tail))
       (case (gslt:rule:row-at $declaration $declarations)
         (((Some (GrammarTypingV1 $label $category $parameters))
           (case (gslt:rule:row-at $index $parameters)
             (((Some $parameter)
               (let $filled (gslt:rule:scope-fill $inner $target)
                 (if (gslt:premise:parameter-representation $parameter $filled)
                     (gslt:rule:site-replacement-represented $declarations $inner $tail $target)
                     False)))
              ($_ False))))
          ((Some (GrammarTypingWrappedV1 $label $category $parameters))
           (case (gslt:rule:row-at $index $parameters)
             (((Some $parameter)
               (let $filled (gslt:rule:scope-fill $inner $target)
                 (if (gslt:premise:parameter-representation $parameter $filled)
                     (gslt:rule:site-replacement-represented $declarations $inner $tail $target)
                     False)))
              ($_ False))))
          ($_ False))))
      ((ReplacementShape (ContextLam $binder $inner) (LCons (TypingLambda $domain) $tail))
       (gslt:rule:site-replacement-represented $declarations $inner $tail $target))
      ((ReplacementShape (ContextMultiLam $arity $binders $inner)
                         (LCons (TypingMultiLambda $frameArity $domain) $tail))
       (gslt:rule:site-replacement-represented $declarations $inner $tail $target))
      ((ReplacementShape (ContextCollection $kind $before $inner $after $rest)
                         (LCons (TypingDirectCollection $frameKind) $tail))
       (gslt:rule:site-replacement-represented $declarations $inner $tail $target))
      ((ReplacementShape (ContextCollection $kind $before $inner $after $rest)
                         (LCons (TypingAuthoredCollection $declaration) $tail))
       (gslt:rule:site-replacement-represented $declarations $inner $tail $target))
      ($_ False))))

(: gslt:rule:job-finish-root (-> Atom Atom %Undefined%))
(= (gslt:rule:job-finish-root $request $result)
   (case (RuleJobFinishInput $request $result)
     (((RuleJobFinishInput
         (RuleJobRequestProjection
           (PremiseEnvironment $declarations $rewrites $specifications $provider $reflection $free)
           $permissions $bound $expected $source
           (RuleJob $ordinal $declaration
             (RuleJobSite $address $context $focus $focusBound $focusType $frames)))
         (PremiseResult $goal (RootAnswer $trace $captured $completed $history $localTarget)))
       (if (== $goal (RootGoal $focusBound $focusType $focus $ordinal))
         (if (gslt:rule:scope-permitted $permissions $context)
           (if (gslt:rule:site-replacement-represented $declarations $context $frames $localTarget)
             (let $target (gslt:rule:scope-fill $context $localTarget)
               (if (gslt:premise:open-well-sorted $declarations $free $bound $expected $target)
                 (Some (RuleJobReceipt
                   (RuleJob $ordinal $declaration
                     (RuleJobSite $address $context $focus $focusBound $focusType $frames))
                   $trace $captured $completed $history $localTarget $target))
                 None))
             None)
           None)
         None))
      ($_ None))))

(: gslt:premise:matching-environment (-> Atom %Undefined%))
(= (gslt:premise:matching-environment $environment)
   (case $environment
     (((InterpretedPremiseEnvironment $names $core) $core)
      ($ordinary $ordinary))))
(: gslt:premise:matching-start (-> Atom Atom %Undefined%))
(= (gslt:premise:matching-start $environment $request)
   (case $environment
     (((InterpretedPremiseEnvironment $names $core)
       (gslt:recursive-collection:canonical-start $names $request))
      ($ordinary (gslt:rule:scope-matcher-start $request)))))
(: gslt:premise:matching-tick (-> Atom Atom Atom %Undefined%))
(= (gslt:premise:matching-tick $environment $request $state)
   (case $environment
     (((InterpretedPremiseEnvironment $names $core)
       (gslt:recursive-collection:canonical-tick $names $state))
      ($ordinary (gslt:rule:scope-matcher-tick $request $state)))))
(: gslt:premise:matching-complete (-> Atom Atom %Undefined%))
(= (gslt:premise:matching-complete $environment $state)
   (case $environment
     (((InterpretedPremiseEnvironment $names $core)
       (gslt:recursive-collection:canonical-complete $state))
      ($ordinary (gslt:rule:scope-matcher-complete $state)))))
(: gslt:premise:matching-answer-at (-> Atom Atom Atom %Undefined%))
(= (gslt:premise:matching-answer-at $environment $state $cursor)
   (case $environment
     (((InterpretedPremiseEnvironment $names $core)
       (gslt:recursive-collection:canonical-answer-at $state $cursor))
      ($ordinary
       (case $state
         (((ScopedMatcherState $agenda $answers) (gslt:rule:row-at $cursor $answers))
          ($bad None)))))))
(: gslt:premise:matching-input (-> Atom Atom Atom %Undefined%))
(= (gslt:premise:matching-input $environment $actual $expected)
   (case $environment
     (((InterpretedPremiseEnvironment $names $core)
       (gslt:recursive-collection:canonical-input $names $actual $expected))
      ($ordinary (== $actual $expected)))))
