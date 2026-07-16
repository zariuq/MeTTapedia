; Semantic projection of a checked ordered Metamath statement ledger.  The
; source ledger retains syntax order, spans, scopes, and proof payloads; this
; projection retains only the final declaration database shared with the
; independent source reader.

!(import! &self metamath_statement_ledger_v0)

; ---------- Lists and finite sets -----------------------------------------

(= (mm-semantic:append Nil $right) $right)
(= (mm-semantic:append (Cons $head $tail) $right)
   (Cons $head (mm-semantic:append $tail $right)))

(= (mm-semantic:length Nil) 0)
(= (mm-semantic:length (Cons $head $tail))
   (+ 1 (mm-semantic:length $tail)))

(= (mm-semantic:member $value Nil) False)
(= (mm-semantic:member $value (Cons $head $tail))
   (if (== $value $head)
     True
     (mm-semantic:member $value $tail)))

(= (mm-semantic:add-unique $value $values)
   (if (mm-semantic:member $value $values)
     $values
     (mm-semantic:append $values (Cons $value Nil))))

(= (mm-semantic:add-all-unique Nil $values) $values)
(= (mm-semantic:add-all-unique (Cons $head $tail) $values)
   (mm-semantic:add-all-unique $tail
     (mm-semantic:add-unique $head $values)))

(= (mm-semantic:pair-equal
      (MMSemanticPair $left-a $right-a)
      (MMSemanticPair $left-b $right-b))
   (or
     (and (== $left-a $left-b) (== $right-a $right-b))
     (and (== $left-a $right-b) (== $right-a $left-b))))

(= (mm-semantic:pair-member $pair Nil) False)
(= (mm-semantic:pair-member $pair (Cons $head $tail))
   (if (mm-semantic:pair-equal $pair $head)
     True
     (mm-semantic:pair-member $pair $tail)))

(= (mm-semantic:add-pair-unique $pair $pairs)
   (if (mm-semantic:pair-member $pair $pairs)
     $pairs
     (mm-semantic:append $pairs (Cons $pair Nil))))

(= (mm-semantic:pairs-with $left Nil $pairs) $pairs)
(= (mm-semantic:pairs-with $left (Cons $right $rest) $pairs)
   (mm-semantic:pairs-with $left $rest
     (mm-semantic:add-pair-unique
       (MMSemanticPair $left $right) $pairs)))

(= (mm-semantic:all-pairs Nil $pairs) $pairs)
(= (mm-semantic:all-pairs (Cons $head $tail) $pairs)
   (mm-semantic:all-pairs $tail
     (mm-semantic:pairs-with $head $tail $pairs)))

(= (mm-semantic:pair-set-subset Nil $right) True)
(= (mm-semantic:pair-set-subset (Cons $pair $rest) $right)
   (and (mm-semantic:pair-member $pair $right)
        (mm-semantic:pair-set-subset $rest $right)))

(= (mm-semantic:pair-set-equal $left $right)
   (and (== (mm-semantic:length $left) (mm-semantic:length $right))
        (mm-semantic:pair-set-subset $left $right)))

; ---------- Symbols and source frames -------------------------------------

(= (mm-semantic:symbol $variables $token)
   (if (mm-semantic:member $token $variables)
     (MMSemanticVariableSymbol $token)
     (MMSemanticConstantSymbol $token)))

(= (mm-semantic:symbols $variables Nil) Nil)
(= (mm-semantic:symbols $variables (Cons $token $rest))
   (Cons (mm-semantic:symbol $variables $token)
     (mm-semantic:symbols $variables $rest)))

(= (mm-semantic:variables-in-formula $variables Nil $found) $found)
(= (mm-semantic:variables-in-formula
      $variables (Cons $token $rest) $found)
   (mm-semantic:variables-in-formula $variables $rest
     (if (mm-semantic:member $token $variables)
       (mm-semantic:add-unique $token $found)
       $found)))

(= (mm-semantic:essential-variables $variables Nil $found) $found)
(= (mm-semantic:essential-variables
      $variables
      (Cons (MMSemanticFloat $label $typecode $variable) $rest)
      $found)
   (mm-semantic:essential-variables $variables $rest $found))
(= (mm-semantic:essential-variables
      $variables
      (Cons (MMSemanticEssential $label $formula) $rest)
      $found)
   (mm-semantic:essential-variables $variables $rest
     (mm-semantic:variables-in-formula $variables $formula $found)))

(= (mm-semantic:used-variables $variables $active $formula)
   (mm-semantic:essential-variables $variables $active
     (mm-semantic:variables-in-formula $variables $formula Nil)))

(= (mm-semantic:hypothesis-labels Nil) Nil)
(= (mm-semantic:hypothesis-labels
      (Cons (MMSemanticFloat $label $typecode $variable) $rest))
   (Cons $label (mm-semantic:hypothesis-labels $rest)))
(= (mm-semantic:hypothesis-labels
      (Cons (MMSemanticEssential $label $formula) $rest))
   (Cons $label (mm-semantic:hypothesis-labels $rest)))

(= (mm-semantic:mandatory-labels Nil $used) Nil)
(= (mm-semantic:mandatory-labels
      (Cons (MMSemanticFloat $label $typecode $variable) $rest) $used)
   (if (mm-semantic:member $variable $used)
     (Cons $label (mm-semantic:mandatory-labels $rest $used))
     (mm-semantic:mandatory-labels $rest $used)))
(= (mm-semantic:mandatory-labels
      (Cons (MMSemanticEssential $label $formula) $rest) $used)
   (Cons $label (mm-semantic:mandatory-labels $rest $used)))

(= (mm-semantic:filter-dv Nil $used) Nil)
(= (mm-semantic:filter-dv
      (Cons (MMSemanticPair $left $right) $rest) $used)
   (if (and (mm-semantic:member $left $used)
            (mm-semantic:member $right $used))
     (Cons (MMSemanticPair $left $right)
       (mm-semantic:filter-dv $rest $used))
     (mm-semantic:filter-dv $rest $used)))

; ---------- Semantic objects ----------------------------------------------

(= (mm-semantic:declare-constants Nil $objects) $objects)
(= (mm-semantic:declare-constants (Cons $name $rest) $objects)
   (mm-semantic:declare-constants $rest
     (mm-semantic:append $objects
       (Cons
         (MMSemanticEntry $name (MMSemanticConstant $name))
         Nil))))

(= (mm-semantic:declare-variables Nil $variables $objects)
   (MMSemanticDeclarations $variables $objects))
(= (mm-semantic:declare-variables
      (Cons $name $rest) $variables $objects)
   (mm-semantic:declare-variables $rest
     (mm-semantic:add-unique $name $variables)
     (mm-semantic:append $objects
       (Cons
         (MMSemanticEntry $name (MMSemanticVariable $name))
         Nil))))

(= (mm-semantic:hypothesis-object
      $variables (MMSemanticFloat $label $typecode $variable))
   (MMSemanticEntry $label
     (MMSemanticHypothesis False
       (mm-semantic:symbols $variables
         (Cons $typecode (Cons $variable Nil)))
       $label)))
(= (mm-semantic:hypothesis-object
      $variables (MMSemanticEssential $label $formula))
   (MMSemanticEntry $label
     (MMSemanticHypothesis True
       (mm-semantic:symbols $variables $formula)
       $label)))

(= (mm-semantic:assertion-object
      $variables $active $dv $label $formula)
   (let $used (mm-semantic:used-variables $variables $active $formula)
     (MMSemanticEntry $label
       (MMSemanticAssertion
         (mm-semantic:symbols $variables $formula)
         (mm-semantic:filter-dv $dv $used)
         (mm-semantic:mandatory-labels $active $used)
         $label))))

; ---------- Ordered-ledger interpretation ---------------------------------

(= (mm-semantic:interpret
      Nil $scopes $active $dv $variables $objects)
   (case $scopes
     ((Nil
       (MMSemanticDatabase
         $dv (mm-semantic:hypothesis-labels $active) $objects))
      ($_ (MMSemanticProjectionError unclosed-scope)))))

(= (mm-semantic:interpret
      (Cons $entry $rest) $scopes $active $dv $variables $objects)
   (case $entry
     (((MMStatementConst $span $symbols)
       (mm-semantic:interpret $rest $scopes $active $dv $variables
         (mm-semantic:declare-constants $symbols $objects)))
      ((MMStatementVar $span $symbols)
       (case (mm-semantic:declare-variables $symbols $variables $objects)
         (((MMSemanticDeclarations $next-variables $next-objects)
           (mm-semantic:interpret $rest $scopes $active $dv
             $next-variables $next-objects)))))
      ((MMStatementDisjoint $span $symbols)
       (mm-semantic:interpret $rest $scopes $active
         (mm-semantic:all-pairs $symbols $dv) $variables $objects))
      ((MMStatementFloat $span $label $typecode $variable)
       (let $hypothesis (MMSemanticFloat $label $typecode $variable)
         (mm-semantic:interpret $rest $scopes
           (mm-semantic:append $active (Cons $hypothesis Nil))
           $dv $variables
           (mm-semantic:append $objects
             (Cons
               (mm-semantic:hypothesis-object $variables $hypothesis)
               Nil)))))
      ((MMStatementEssential $span $label $formula)
       (let $hypothesis (MMSemanticEssential $label $formula)
         (mm-semantic:interpret $rest $scopes
           (mm-semantic:append $active (Cons $hypothesis Nil))
           $dv $variables
           (mm-semantic:append $objects
             (Cons
               (mm-semantic:hypothesis-object $variables $hypothesis)
               Nil)))))
      ((MMStatementAxiom $span $label $formula)
       (mm-semantic:interpret $rest $scopes $active $dv $variables
         (mm-semantic:append $objects
           (Cons
             (mm-semantic:assertion-object
               $variables $active $dv $label $formula)
             Nil))))
      ((MMStatementTheorem $span $label $formula $proof)
       (mm-semantic:interpret $rest $scopes $active $dv $variables
         (mm-semantic:append $objects
           (Cons
             (mm-semantic:assertion-object
               $variables $active $dv $label $formula)
             Nil))))
      ((MMStatementScopeOpen $span)
       (mm-semantic:interpret $rest
         (Cons (MMSemanticScope $active $dv) $scopes)
         $active $dv $variables $objects))
      ((MMStatementScopeClose $span)
       (case $scopes
         (((Cons (MMSemanticScope $outer-active $outer-dv) $outer-scopes)
           (mm-semantic:interpret $rest $outer-scopes
             $outer-active $outer-dv $variables $objects))
          ($_ (MMSemanticProjectionError unmatched-scope-close)))))
      ((MMStatementInclude $span $path)
       (MMSemanticProjectionError include-resolution-required))
      ($_ (MMSemanticProjectionError malformed-ledger-entry)))))

(= (mm-semantic:project $ledger)
   (case $ledger
     (((MMCheckedStatementLedger
          (MMSourceIdentityV0 $revision $digest)
          $tokens $nodes $entries)
       (case (mm-semantic:interpret $entries Nil Nil Nil Nil Nil)
         (((MMSemanticDatabase $dv $hypotheses $objects)
           (MMSemanticReference $revision $digest
             (MMSemanticDatabase $dv $hypotheses $objects)))
          ($error $error))))
      ((MMIncludeResolutionRequired $identity $tokens $nodes $entries)
       (MMSemanticProjectionError include-resolution-required))
      ($error $error))))

; ---------- Order-independent comparison ----------------------------------

(= (mm-semantic:object-equal $left $right)
   (case (Cons $left (Cons $right Nil))
     (((Cons (MMSemanticConstant $left-name)
             (Cons (MMSemanticConstant $right-name) Nil))
       (== $left-name $right-name))
      ((Cons (MMSemanticVariable $left-name)
             (Cons (MMSemanticVariable $right-name) Nil))
       (== $left-name $right-name))
      ((Cons
         (MMSemanticHypothesis $essential-a $formula-a $label-a)
         (Cons
           (MMSemanticHypothesis $essential-b $formula-b $label-b) Nil))
       (and (== $essential-a $essential-b)
         (and (== $formula-a $formula-b) (== $label-a $label-b))))
      ((Cons
         (MMSemanticAssertion $formula-a $dv-a $hypotheses-a $label-a)
         (Cons
           (MMSemanticAssertion $formula-b $dv-b $hypotheses-b $label-b)
           Nil))
       (and (== $formula-a $formula-b)
         (and (mm-semantic:pair-set-equal $dv-a $dv-b)
           (and (== $hypotheses-a $hypotheses-b)
                (== $label-a $label-b)))))
      ($_ False))))

(= (mm-semantic:find-object $label Nil) MMSemanticObjectNotFound)
(= (mm-semantic:find-object
      $label (Cons (MMSemanticEntry $candidate $object) $rest))
   (if (== $label $candidate)
     (MMSemanticObjectFound $object)
     (mm-semantic:find-object $label $rest)))

(= (mm-semantic:objects-subset Nil $actual) True)
(= (mm-semantic:objects-subset
      (Cons (MMSemanticEntry $label $expected) $rest) $actual)
   (case (mm-semantic:find-object $label $actual)
     (((MMSemanticObjectFound $found)
       (and (mm-semantic:object-equal $expected $found)
            (mm-semantic:objects-subset $rest $actual)))
      (MMSemanticObjectNotFound False))))

(= (mm-semantic:database-equal
      (MMSemanticDatabase $dv-a $hypotheses-a $objects-a)
      (MMSemanticDatabase $dv-b $hypotheses-b $objects-b))
   (and (mm-semantic:pair-set-equal $dv-a $dv-b)
     (and (== $hypotheses-a $hypotheses-b)
       (and (== (mm-semantic:length $objects-a)
                (mm-semantic:length $objects-b))
            (mm-semantic:objects-subset $objects-a $objects-b)))))

(= (mm-semantic:reference-equal
      (MMSemanticReference $revision-a $digest-a $database-a)
      (MMSemanticReference $revision-b $digest-b $database-b))
   (and (== $revision-a $revision-b)
     (and (== $digest-a $digest-b)
          (mm-semantic:database-equal $database-a $database-b))))

(= (mm-semantic:agrees $ledger $reference)
   (case (mm-semantic:project $ledger)
     (((MMSemanticReference $revision $digest $database)
       (mm-semantic:reference-equal
         (MMSemanticReference $revision $digest $database)
         $reference))
      ($error False))))
