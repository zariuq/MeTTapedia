; =============================================================================
; generic_inference_checker_v0.metta
;
; Executable proof-relevant checker for finite inference languages.
;
; The serialized language carries ordinary term constructors, judgment
; heads, and ordered rule schemas.  Raw proof trees carry a rule identifier,
; ordered schema arguments, and ordered child proofs.  Admission and checking
; both fail closed.
;
; This is the operational counterpart of LanguageDef/InferenceChecker.lean.
; It shares the MIK binding waist's de Bruijn variable and depth discipline;
; explicit Pattern substitutions remain syntax during schema instantiation.
; =============================================================================

!(import! &self kernel_binding_decl_v1)

; ---------- Serialized Pattern and language data ------------------------
; Pattern:
;   (Var n)                         shared de Bruijn variable
;   (FVar name)                     schema metavariable
;   (PApp head arguments)
;   (PLam BNone body)               canonical one-binder form
;   (PMultiLam arity LNil body)     canonical many-binder form
;   (PSubst body replacement)       explicit substitution syntax
;   (PCollection kind elements RNone)
;
; Lists use LNil / (LCons head tail).
;
; Language:
;   (GInferenceLanguageV1 1 constructors judgments rules conversion)
;   (CDecl head arity)
;   (JDecl head arity)
;   (GRuleV1 id formals premises conclusion side-conditions)
;   (Formal name occurrence-depth)
;   GNoConversion | (GConversion judgment-head version)
;
; Proof:
;   (GProof (GRuleInst rule-id arguments) children)

; ---------- Small total list utilities --------------------------------------
(= (gic-append LNil $ys) $ys)
(= (gic-append (LCons $x $xs) $ys)
   (LCons $x (gic-append $xs $ys)))

(= (gic-member $x LNil) False)
(= (gic-member $x (LCons $y $ys))
   (if (== $x $y) True (gic-member $x $ys)))

(= (gic-no-duplicates LNil) True)
(= (gic-no-duplicates (LCons $x $xs))
   (if (gic-member $x $xs) False (gic-no-duplicates $xs)))

(= (gic-all-members LNil $ys) True)
(= (gic-all-members (LCons $x $xs) $ys)
   (if (gic-member $x $ys) (gic-all-members $xs $ys) False))

(= (gic-list-length LNil) 0)
(= (gic-list-length (LCons $x $xs)) (+ 1 (gic-list-length $xs)))

(= (gic-list-get LNil $index) GICNoListValue)
(= (gic-list-get (LCons $head $tail) $index)
   (if (== $index 0)
     (GICListValue $head)
     (if (> $index 0)
       (gic-list-get $tail (- $index 1))
       GICNoListValue)))

; ---------- Pattern closure and canonical binding metadata ------------------
(= (gic-ground-list-at $depth LNil) True)
(= (gic-ground-list-at $depth (LCons $pattern $rest))
   (if (gic-ground-at $depth $pattern)
     (gic-ground-list-at $depth $rest)
     False))

(= (gic-ground-at $depth $pattern)
   (case $pattern
     (((Var $index) (< $index $depth))
      ((FVar $name) False)
      ((PApp $head $arguments) (gic-ground-list-at $depth $arguments))
      ((PLam $binder $body) (gic-ground-at (+ $depth 1) $body))
      ((PMultiLam $arity $binders $body)
        (if (binding-depth-ok $arity)
          (gic-ground-at (+ $depth $arity) $body)
          False))
      ((PSubst $body $replacement)
        (if (gic-ground-at (+ $depth 1) $body)
          (gic-ground-at $depth $replacement)
          False))
      ((PCollection $kind $elements RNone)
        (gic-ground-list-at $depth $elements))
      ((PCollection $kind $elements (RSome $name)) False)
      ($_ False))))

(= (gic-scoped-list-at $depth LNil) True)
(= (gic-scoped-list-at $depth (LCons $pattern $rest))
   (if (gic-scoped-at $depth $pattern)
     (gic-scoped-list-at $depth $rest)
     False))

(= (gic-scoped-at $depth $pattern)
   (case $pattern
     (((Var $index) (< $index $depth))
      ((FVar $name) True)
      ((PApp $head $arguments) (gic-scoped-list-at $depth $arguments))
      ((PLam $binder $body) (gic-scoped-at (+ $depth 1) $body))
      ((PMultiLam $arity $binders $body)
        (if (binding-depth-ok $arity)
          (gic-scoped-at (+ $depth $arity) $body)
          False))
      ((PSubst $body $replacement)
        (if (gic-scoped-at (+ $depth 1) $body)
          (gic-scoped-at $depth $replacement)
          False))
      ((PCollection $kind $elements $rest)
        (gic-scoped-list-at $depth $elements))
      ($_ False))))

(= (gic-canonical-list LNil) True)
(= (gic-canonical-list (LCons $pattern $rest))
   (if (gic-canonical $pattern) (gic-canonical-list $rest) False))

(= (gic-canonical $pattern)
   (case $pattern
     (((Var $index) True)
      ((FVar $name) True)
      ((PApp $head $arguments) (gic-canonical-list $arguments))
      ((PLam BNone $body) (gic-canonical $body))
      ((PLam (BSome $name) $body) False)
      ((PMultiLam $arity LNil $body) (gic-canonical $body))
      ((PMultiLam $arity (LCons $name $names) $body) False)
      ((PSubst $body $replacement)
        (if (gic-canonical $body) (gic-canonical $replacement) False))
      ((PCollection $kind $elements $rest) (gic-canonical-list $elements))
      ($_ False))))

(= (gic-no-rest-list LNil) True)
(= (gic-no-rest-list (LCons $pattern $rest))
   (if (gic-no-collection-rest $pattern)
     (gic-no-rest-list $rest)
     False))

(= (gic-no-collection-rest $pattern)
   (case $pattern
     (((Var $index) True)
      ((FVar $name) True)
      ((PApp $head $arguments) (gic-no-rest-list $arguments))
      ((PLam $binder $body) (gic-no-collection-rest $body))
      ((PMultiLam $arity $binders $body) (gic-no-collection-rest $body))
      ((PSubst $body $replacement)
        (if (gic-no-collection-rest $body)
          (gic-no-collection-rest $replacement)
          False))
      ((PCollection $kind $elements RNone) (gic-no-rest-list $elements))
      ((PCollection $kind $elements (RSome $name)) False)
      ($_ False))))

; ---------- Exact-depth metavariable occurrence accounting -----------------
(= (gic-occurrences-list-at $depth LNil) LNil)
(= (gic-occurrences-list-at $depth (LCons $pattern $rest))
   (gic-append
     (gic-occurrences-at $depth $pattern)
     (gic-occurrences-list-at $depth $rest)))

(= (gic-occurrences-at $depth $pattern)
   (case $pattern
     (((Var $index) LNil)
      ((FVar $name) (LCons (Formal $name $depth) LNil))
      ((PApp $head $arguments) (gic-occurrences-list-at $depth $arguments))
      ((PLam $binder $body) (gic-occurrences-at (+ $depth 1) $body))
      ((PMultiLam $arity $binders $body)
        (gic-occurrences-at (+ $depth $arity) $body))
      ((PSubst $body $replacement)
        (gic-append
          (gic-occurrences-at (+ $depth 1) $body)
          (gic-occurrences-at $depth $replacement)))
      ((PCollection $kind $elements $rest)
        (gic-occurrences-list-at $depth $elements))
      ($_ LNil))))

(= (gic-formal-names LNil) LNil)
(= (gic-formal-names (LCons (Formal $name $depth) $rest))
   (LCons $name (gic-formal-names $rest)))

(= (gic-nonempty-formal-names LNil) True)
(= (gic-nonempty-formal-names (LCons (Formal $name $depth) $rest))
   (if (== $name "") False (gic-nonempty-formal-names $rest)))

; ---------- Constructor and judgment signatures ----------------------------
(= (gic-constructor-heads LNil) LNil)
(= (gic-constructor-heads (LCons (CDecl $head $arity) $rest))
   (LCons $head (gic-constructor-heads $rest)))

(= (gic-judgment-heads LNil) LNil)
(= (gic-judgment-heads (LCons (JDecl $head $arity) $rest))
   (LCons $head (gic-judgment-heads $rest)))

(= (gic-decls-nonempty LNil) True)
(= (gic-decls-nonempty (LCons (CDecl $head $arity) $rest))
   (if (== $head "") False (gic-decls-nonempty $rest)))

(= (gic-judgments-nonempty LNil) True)
(= (gic-judgments-nonempty (LCons (JDecl $head $arity) $rest))
   (if (== $head "") False (gic-judgments-nonempty $rest)))

(= (gic-has-constructor-arity LNil $head $arity) False)
(= (gic-has-constructor-arity (LCons (CDecl $candidate $n) $rest) $head $arity)
   (if (== $candidate $head)
     (== $n $arity)
     (gic-has-constructor-arity $rest $head $arity)))

(= (gic-has-judgment-arity LNil $head $arity) False)
(= (gic-has-judgment-arity (LCons (JDecl $candidate $n) $rest) $head $arity)
   (if (== $candidate $head)
     (== $n $arity)
     (gic-has-judgment-arity $rest $head $arity)))

(= (gic-fixed-list-valid $constructors LNil) True)
(= (gic-fixed-list-valid $constructors (LCons $pattern $rest))
   (if (gic-fixed-valid $constructors $pattern)
     (gic-fixed-list-valid $constructors $rest)
     False))

(= (gic-fixed-valid $constructors $pattern)
   (case $pattern
     (((Var $index) True)
      ((FVar $name) True)
      ((PApp $head $arguments)
        (if (gic-has-constructor-arity
              $constructors $head (gic-list-length $arguments))
          (gic-fixed-list-valid $constructors $arguments)
          False))
      ((PLam $binder $body) (gic-fixed-valid $constructors $body))
      ((PMultiLam $arity $binders $body) (gic-fixed-valid $constructors $body))
      ((PSubst $body $replacement)
        (if (gic-fixed-valid $constructors $body)
          (gic-fixed-valid $constructors $replacement)
          False))
      ((PCollection $kind $elements $rest)
        (gic-fixed-list-valid $constructors $elements))
      ($_ False))))

(= (gic-judgment-schema-valid $constructors $judgments $pattern)
   (case $pattern
     (((PApp $head $arguments)
        (if (gic-has-judgment-arity
              $judgments $head (gic-list-length $arguments))
          (gic-fixed-list-valid $constructors $arguments)
          False))
      ($_ False))))

(= (gic-judgment-signature-disjoint LNil $constructor-heads) True)
(= (gic-judgment-signature-disjoint (LCons $head $rest) $constructor-heads)
   (if (gic-member $head $constructor-heads)
     False
     (if (gic-member $head
           (LCons "$zip" (LCons "$map" (LCons "$eval" LNil))))
       False
       (gic-judgment-signature-disjoint $rest $constructor-heads))))

; Generic rule obligations are part of the language rather than an external
; validator.  Each positional reference must name a formal at the exact
; ambient depth required by the operation.
(= (gic-formal-depth-equals $formals $index $expected)
   (case (gic-list-get $formals $index)
     (((GICListValue (Formal $name $depth)) (== $depth $expected))
      ($_ False))))

(= (gic-side-condition-valid $formals $condition)
   (case $condition
     (((GExplicitSubstitution
          $ambient $body-index $replacement-index $result-index)
        (if (gic-formal-depth-equals
              $formals $body-index (+ $ambient 1))
          (if (gic-formal-depth-equals
                $formals $replacement-index $ambient)
            (gic-formal-depth-equals $formals $result-index $ambient)
            False)
          False))
      ((GUnusedBinderElimination $ambient $body-index $result-index)
        (if (gic-formal-depth-equals
              $formals $body-index (+ $ambient 1))
          (gic-formal-depth-equals $formals $result-index $ambient)
          False))
      ($_ False))))

(= (gic-side-conditions-valid $formals LNil) True)
(= (gic-side-conditions-valid $formals (LCons $condition $rest))
   (if (gic-side-condition-valid $formals $condition)
     (gic-side-conditions-valid $formals $rest)
     False))

(= (gic-conversion-valid $judgments $conversion)
   (case $conversion
     ((GNoConversion True)
      ((GConversion $head $version)
        (if (== $head "")
          False
          (if (== $version "")
            False
            (gic-has-judgment-arity $judgments $head 2))))
      ($_ False))))

; ---------- Language admission ------------------------------------------
(= (gic-pattern-list-valid $patterns)
   (if (gic-scoped-list-at 0 $patterns)
     (if (gic-no-rest-list $patterns) (gic-canonical-list $patterns) False)
     False))

(= (gic-judgment-list-valid $constructors $judgments LNil) True)
(= (gic-judgment-list-valid $constructors $judgments
      (LCons $pattern $rest))
   (if (gic-judgment-schema-valid $constructors $judgments $pattern)
     (gic-judgment-list-valid $constructors $judgments $rest)
     False))

(= (gic-rule-valid $constructors $judgments
      (GRuleV1 $id $formals $premises $conclusion $side-conditions))
   (let $patterns (gic-append $premises (LCons $conclusion LNil))
     (let $occurrences (gic-occurrences-list-at 0 $patterns)
       (if (== $id "") False
         (if (gic-nonempty-formal-names $formals)
           (if (gic-no-duplicates (gic-formal-names $formals))
             (if (gic-all-members $occurrences $formals)
               (if (gic-all-members $formals $occurrences)
                 (if (gic-pattern-list-valid $patterns)
                   (if (gic-judgment-list-valid
                         $constructors $judgments $patterns)
                     (gic-side-conditions-valid $formals $side-conditions)
                     False)
                   False)
                 False)
               False)
             False)
           False)))))

(= (gic-rule-ids LNil) LNil)
(= (gic-rule-ids
      (LCons
        (GRuleV1 $id $formals $premises $conclusion $side-conditions)
        $rest))
   (LCons $id (gic-rule-ids $rest)))

(= (gic-rules-valid $constructors $judgments LNil) True)
(= (gic-rules-valid $constructors $judgments (LCons $rule $rest))
   (if (gic-rule-valid $constructors $judgments $rule)
     (gic-rules-valid $constructors $judgments $rest)
     False))

(= (gic-language-parts-valid
      $constructors $judgments $rules $conversion)
   (let $constructor-heads (gic-constructor-heads $constructors)
     (let $judgment-heads (gic-judgment-heads $judgments)
       (if (gic-decls-nonempty $constructors)
         (if (gic-no-duplicates $constructor-heads)
           (if (gic-judgments-nonempty $judgments)
             (if (gic-no-duplicates $judgment-heads)
               (if (gic-judgment-signature-disjoint
                     $judgment-heads $constructor-heads)
                 (if (gic-no-duplicates (gic-rule-ids $rules))
                   (if (gic-rules-valid $constructors $judgments $rules)
                     (gic-conversion-valid $judgments $conversion)
                     False)
                   False)
                 False)
               False)
             False)
           False)
         False))))

(= (gic-language-valid $language)
   (case $language
     (((GInferenceLanguageV1
          1 $constructors $judgments $rules $conversion)
        (gic-language-parts-valid
          $constructors $judgments $rules $conversion))
      ($_ False))))

; ---------- Exact argument validation and schema instantiation --------------
(= (gic-arguments-valid $formals $arguments)
   (case (GICPair $formals $arguments)
     (((GICPair LNil LNil) True)
      ((GICPair
         (LCons (Formal $name $depth) $more-formals)
         (LCons $argument $more-arguments))
        (if (gic-ground-at $depth $argument)
          (if (gic-canonical $argument)
            (gic-arguments-valid $more-formals $more-arguments)
            False)
          False))
      ($_ False))))

; The indexed checker validates shared argument subterms once.  This is the
; same conjunction of gic-ground-at and gic-canonical used above; the index
; only remembers successful results at an exact binder depth.  In a
; chronological proof DAG, a child derivation is therefore available before
; a parent argument refers to it, avoiding repeated descent through a shared
; derivation tree without changing the accepted judgment.
(= (gic-index-argument-known $space $depth $pattern)
   (case (collapse
           (match $space
             (GICIndexedArgumentValid $depth $pattern)
             GICArgumentKnown))
     (((GICArgumentKnown) True)
      ($_ False))))

(= (gic-index-pattern-list-valid-at $space $depth LNil) True)
(= (gic-index-pattern-list-valid-at $space $depth
      (LCons $pattern $rest))
   (if (gic-index-argument-valid-at $space $depth $pattern)
     (gic-index-pattern-list-valid-at $space $depth $rest)
     False))

(= (gic-index-argument-valid-at $space $depth $pattern)
   (if (gic-index-argument-known $space $depth $pattern)
     True
     (let $valid
       (case $pattern
         (((Var $index) (< $index $depth))
          ((FVar $name) False)
          ((PApp $head $arguments)
            (gic-index-pattern-list-valid-at $space $depth $arguments))
          ((PLam BNone $body)
            (gic-index-argument-valid-at $space (+ $depth 1) $body))
          ((PLam (BSome $name) $body) False)
          ((PMultiLam $arity LNil $body)
            (if (binding-depth-ok $arity)
              (gic-index-argument-valid-at
                $space (+ $depth $arity) $body)
              False))
          ((PMultiLam $arity (LCons $name $names) $body) False)
          ((PSubst $body $replacement)
            (if (gic-index-argument-valid-at
                  $space (+ $depth 1) $body)
              (gic-index-argument-valid-at $space $depth $replacement)
              False))
          ((PCollection $kind $elements RNone)
            (gic-index-pattern-list-valid-at $space $depth $elements))
          ((PCollection $kind $elements (RSome $name)) False)
          ($_ False)))
       (if $valid
         (let $added
           (add-atom $space
             (GICIndexedArgumentValid $depth $pattern))
           True)
         False))))

(= (gic-index-arguments-valid $space $formals $arguments)
   (case (GICPair $formals $arguments)
     (((GICPair LNil LNil) True)
      ((GICPair
         (LCons (Formal $name $depth) $more-formals)
         (LCons $argument $more-arguments))
        (if (gic-index-argument-valid-at $space $depth $argument)
          (gic-index-arguments-valid
            $space $more-formals $more-arguments)
          False))
      ($_ False))))

(= (gic-lookup-argument $formals $arguments $target $depth)
   (case (GICPair $formals $arguments)
     (((GICPair
         (LCons (Formal $name $formal-depth) $more-formals)
         (LCons $argument $more-arguments))
        (if (== (Formal $name $formal-depth) (Formal $target $depth))
          (FoundArgument $argument)
          (gic-lookup-argument
            $more-formals $more-arguments $target $depth)))
      ($_ NoArgument))))

(= (gic-instantiate-list $formals $arguments $depth LNil) (PatternsOK LNil))
(= (gic-instantiate-list $formals $arguments $depth
      (LCons $schema $schemas))
   (case (gic-instantiate $formals $arguments $depth $schema)
     (((PatternOK $result)
        (case (gic-instantiate-list $formals $arguments $depth $schemas)
          (((PatternsOK $results) (PatternsOK (LCons $result $results)))
           ($_ PatternsFail))))
      ($_ PatternsFail))))

(= (gic-instantiate $formals $arguments $depth $schema)
   (case $schema
     (((Var $index) (PatternOK (Var $index)))
      ((FVar $name)
        (case (gic-lookup-argument
                $formals $arguments $name $depth)
          (((FoundArgument $argument) (PatternOK $argument))
           ($_ PatternFail))))
      ((PApp $head $schemas)
        (case (gic-instantiate-list $formals $arguments $depth $schemas)
          (((PatternsOK $results) (PatternOK (PApp $head $results)))
           ($_ PatternFail))))
      ((PLam $binder $body)
        (case (gic-instantiate
                $formals $arguments (+ $depth 1) $body)
          (((PatternOK $result) (PatternOK (PLam $binder $result)))
           ($_ PatternFail))))
      ((PMultiLam $arity $binders $body)
        (case (gic-instantiate
                $formals $arguments (+ $depth $arity) $body)
          (((PatternOK $result)
            (PatternOK (PMultiLam $arity $binders $result)))
           ($_ PatternFail))))
      ((PSubst $body $replacement)
        (case (gic-instantiate
                $formals $arguments (+ $depth 1) $body)
          (((PatternOK $body-result)
            (case (gic-instantiate
                    $formals $arguments $depth $replacement)
              (((PatternOK $replacement-result)
                (PatternOK (PSubst $body-result $replacement-result)))
               ($_ PatternFail))))
           ($_ PatternFail))))
      ((PCollection $kind $schemas RNone)
        (case (gic-instantiate-list $formals $arguments $depth $schemas)
          (((PatternsOK $results)
            (PatternOK (PCollection $kind $results RNone)))
           ($_ PatternFail))))
      ((PCollection $kind $schemas (RSome $name)) PatternFail)
      ($_ PatternFail))))

; ---------- Executable generic side conditions -----------------------------
; These operations mirror the Pattern substitution authority.  They are
; defined over the same serialized Pattern carrier, so guarded and unguarded
; rule schemas cannot collapse merely by crossing the runtime wire.
(= (gic-lift-bvars-list $cutoff $shift LNil) LNil)
(= (gic-lift-bvars-list $cutoff $shift (LCons $pattern $rest))
   (LCons
     (gic-lift-bvars $cutoff $shift $pattern)
     (gic-lift-bvars-list $cutoff $shift $rest)))

(= (gic-lift-bvars $cutoff $shift $pattern)
   (case $pattern
     (((Var $index)
        (if (< $index $cutoff)
          (Var $index)
          (Var (+ $index $shift))))
      ((FVar $name) (FVar $name))
      ((PApp $head $arguments)
        (PApp $head (gic-lift-bvars-list $cutoff $shift $arguments)))
      ((PLam $binder $body)
        (PLam $binder (gic-lift-bvars (+ $cutoff 1) $shift $body)))
      ((PMultiLam $arity $binders $body)
        (PMultiLam $arity $binders
          (gic-lift-bvars (+ $cutoff $arity) $shift $body)))
      ((PSubst $body $replacement)
        (PSubst
          (gic-lift-bvars (+ $cutoff 1) $shift $body)
          (gic-lift-bvars $cutoff $shift $replacement)))
      ((PCollection $kind $elements $rest)
        (PCollection $kind
          (gic-lift-bvars-list $cutoff $shift $elements) $rest))
      ($_ (GICBadPattern $pattern)))))

(= (gic-instantiate-bvar-list $depth $replacement LNil) LNil)
(= (gic-instantiate-bvar-list
      $depth $replacement (LCons $pattern $rest))
   (LCons
     (gic-instantiate-bvar-at $depth $replacement $pattern)
     (gic-instantiate-bvar-list $depth $replacement $rest)))

(= (gic-instantiate-bvar-at $depth $replacement $pattern)
   (case $pattern
     (((Var $index)
        (if (< $index $depth)
          (Var $index)
          (if (== $index $depth)
            (gic-lift-bvars 0 $depth $replacement)
            (Var (- $index 1)))))
      ((FVar $name) (FVar $name))
      ((PApp $head $arguments)
        (PApp $head
          (gic-instantiate-bvar-list $depth $replacement $arguments)))
      ((PLam $binder $body)
        (PLam $binder
          (gic-instantiate-bvar-at (+ $depth 1) $replacement $body)))
      ((PMultiLam $arity $binders $body)
        (PMultiLam $arity $binders
          (gic-instantiate-bvar-at
            (+ $depth $arity) $replacement $body)))
      ((PSubst $body $nested-replacement)
        (PSubst
          (gic-instantiate-bvar-at
            (+ $depth 1) $replacement $body)
          (gic-instantiate-bvar-at
            $depth $replacement $nested-replacement)))
      ((PCollection $kind $elements $rest)
        (PCollection $kind
          (gic-instantiate-bvar-list $depth $replacement $elements)
          $rest))
      ($_ (GICBadPattern $pattern)))))

(= (gic-instantiate-bvar $replacement $body)
   (gic-instantiate-bvar-at 0 $replacement $body))

(= (gic-drop-bvar-list $cutoff LNil) (GICDropListOK LNil))
(= (gic-drop-bvar-list $cutoff (LCons $pattern $rest))
   (case (gic-drop-bvar-at $cutoff $pattern)
     (((GICDropOK $head)
        (case (gic-drop-bvar-list $cutoff $rest)
          (((GICDropListOK $tail) (GICDropListOK (LCons $head $tail)))
           ($_ GICDropFail))))
      ($_ GICDropFail))))

(= (gic-drop-bvar-at $cutoff $pattern)
   (case $pattern
     (((Var $index)
        (if (< $index $cutoff)
          (GICDropOK (Var $index))
          (if (== $index $cutoff)
            GICDropFail
            (GICDropOK (Var (- $index 1))))))
      ((FVar $name) (GICDropOK (FVar $name)))
      ((PApp $head $arguments)
        (case (gic-drop-bvar-list $cutoff $arguments)
          (((GICDropListOK $results) (GICDropOK (PApp $head $results)))
           ($_ GICDropFail))))
      ((PLam $binder $body)
        (case (gic-drop-bvar-at (+ $cutoff 1) $body)
          (((GICDropOK $result) (GICDropOK (PLam $binder $result)))
           ($_ GICDropFail))))
      ((PMultiLam $arity $binders $body)
        (case (gic-drop-bvar-at (+ $cutoff $arity) $body)
          (((GICDropOK $result)
            (GICDropOK (PMultiLam $arity $binders $result)))
           ($_ GICDropFail))))
      ((PSubst $body $replacement)
        (case (gic-drop-bvar-at (+ $cutoff 1) $body)
          (((GICDropOK $body-result)
            (case (gic-drop-bvar-at $cutoff $replacement)
              (((GICDropOK $replacement-result)
                (GICDropOK
                  (PSubst $body-result $replacement-result)))
               ($_ GICDropFail))))
           ($_ GICDropFail))))
      ((PCollection $kind $elements $rest)
        (case (gic-drop-bvar-list $cutoff $elements)
          (((GICDropListOK $results)
            (GICDropOK (PCollection $kind $results $rest)))
           ($_ GICDropFail))))
      ($_ GICDropFail))))

(= (gic-drop-bvar $body) (gic-drop-bvar-at 0 $body))

(= (gic-explicit-substitution-holds
      $arguments $body-index $replacement-index $result-index)
   (case (gic-list-get $arguments $body-index)
     (((GICListValue $body)
        (case (gic-list-get $arguments $replacement-index)
          (((GICListValue $replacement)
            (case (gic-list-get $arguments $result-index)
              (((GICListValue $result)
                (== (gic-instantiate-bvar $replacement $body) $result))
               ($_ False))))
           ($_ False))))
      ($_ False))))

(= (gic-unused-binder-elimination-holds
      $arguments $body-index $result-index)
   (case (gic-list-get $arguments $body-index)
     (((GICListValue $body)
        (case (gic-list-get $arguments $result-index)
          (((GICListValue $result)
            (case (gic-drop-bvar $body)
              (((GICDropOK $dropped) (== $dropped $result))
               ($_ False))))
           ($_ False))))
      ($_ False))))

(= (gic-side-condition-holds $arguments $condition)
   (case $condition
     (((GExplicitSubstitution
          $ambient $body-index $replacement-index $result-index)
        (gic-explicit-substitution-holds
          $arguments $body-index $replacement-index $result-index))
      ((GUnusedBinderElimination $ambient $body-index $result-index)
        (gic-unused-binder-elimination-holds
          $arguments $body-index $result-index))
      ($_ False))))

(= (gic-side-conditions-hold $arguments LNil) True)
(= (gic-side-conditions-hold $arguments (LCons $condition $rest))
   (if (gic-side-condition-holds $arguments $condition)
     (gic-side-conditions-hold $arguments $rest)
     False))

; ---------- Rule lookup and proof checking ----------------------------------
(= (gic-lookup-rule LNil $target) NoRule)
(= (gic-lookup-rule
      (LCons
        (GRuleV1 $id $formals $premises $conclusion $side-conditions)
        $rest)
      $target)
   (if (== $id $target)
     (FoundRule
       (GRuleV1 $id $formals $premises $conclusion $side-conditions))
     (gic-lookup-rule $rest $target)))

(= (gic-instantiate-rule $rules (GRuleInst $id $arguments))
   (case (gic-lookup-rule $rules $id)
     (((FoundRule
          (GRuleV1
            $found-id $formals $premises $conclusion $side-conditions))
        (if (gic-arguments-valid $formals $arguments)
          (if (gic-side-conditions-hold $arguments $side-conditions)
            (case (gic-instantiate-list $formals $arguments 0 $premises)
              (((PatternsOK $premise-results)
                (case (gic-instantiate
                        $formals $arguments 0 $conclusion)
                  (((PatternOK $conclusion-result)
                    (RuleOK $premise-results $conclusion-result))
                   ($_ RuleFail))))
               ($_ RuleFail)))
            RuleFail)
          RuleFail))
      ($_ RuleFail))))

(= (gic-check-children $rules $premises $children)
   (case (GICPair $premises $children)
     (((GICPair LNil PrNil) True)
      ((GICPair
         (LCons $premise $more-premises)
         (PrCons $child $more-children))
        (if (gic-check-raw-valid $rules $premise $child)
          (gic-check-children $rules $more-premises $more-children)
          False))
      ($_ False))))

(= (gic-check-raw-valid $rules $goal $proof)
   (case $proof
     (((GProof $rule-instance $children)
        (case (gic-instantiate-rule $rules $rule-instance)
          (((RuleOK $premises $conclusion)
            (if (== $conclusion $goal)
              (gic-check-children $rules $premises $children)
              False))
           ($_ False))))
      ($_ False))))

(= (gic-check $language $goal $proof)
   (if (gic-language-valid $language)
     (case $language
       (((GInferenceLanguageV1
            $version $constructors $judgments $rules $conversion)
          (gic-check-raw-valid $rules $goal $proof))
        ($_ False)))
     False))

(= (gic-check-expected $rules $check)
   (case $check
     (((GCheck $goal $proof True)
        (gic-check-raw-valid $rules $goal $proof))
      ((GCheck $goal $proof False)
        (if (gic-check-raw-valid $rules $goal $proof) False True))
      ($_ False))))

(= (gic-check-batch-valid $rules $checks)
   (case $checks
     ((CheckNil True)
      ((CheckCons $check $rest)
        (if (gic-check-expected $rules $check)
          (gic-check-batch-valid $rules $rest)
          False))
      ($_ False))))

(= (gic-check-batch $language $checks)
   (if (gic-language-valid $language)
     (case $language
       (((GInferenceLanguageV1
            $version $constructors $judgments $rules $conversion)
          (gic-check-batch-valid $rules $checks))
        ($_ False)))
     False))

; ---------- Sequential proof DAG checking ----------------------------------
; Nodes are admitted in list order.  Child identifiers must name earlier
; nodes, so sharing is explicit and cycles/forward references fail closed.
(= (gic-dag-lookup DEnvNil $target) NoDagValue)
(= (gic-dag-lookup (DEnvCons (DVal $id $goal) $rest) $target)
   (if (== $id $target)
     (FoundDagValue $goal)
     (gic-dag-lookup $rest $target)))

(= (gic-dag-children-match $env $premises $child-ids)
   (case (GICDagChildrenPair $premises $child-ids)
     (((GICDagChildrenPair LNil DrNil) True)
      ((GICDagChildrenPair
         (LCons $premise $more-premises)
         (DrCons $child-id $more-child-ids))
        (case (gic-dag-lookup $env $child-id)
          (((FoundDagValue $child-goal)
            (if (== $child-goal $premise)
              (gic-dag-children-match
                $env $more-premises $more-child-ids)
              False))
           ($_ False))))
      ($_ False))))

(= (gic-check-dag-nodes $rules DnNil $env) (DagOK $env))
(= (gic-check-dag-nodes $rules
      (DnCons (GDNode $id $rule-instance $child-ids) $nodes) $env)
   (case (gic-dag-lookup $env $id)
     ((NoDagValue
        (case (gic-instantiate-rule $rules $rule-instance)
          (((RuleOK $premises $conclusion)
            (if (gic-dag-children-match $env $premises $child-ids)
              (gic-check-dag-nodes $rules $nodes
                (DEnvCons (DVal $id $conclusion) $env))
              DagFail))
           ($_ DagFail))))
      ($_ DagFail))))

(= (gic-check-dag-valid $rules $goal $root-id $nodes)
   (case (gic-check-dag-nodes $rules $nodes DEnvNil)
     (((DagOK $env)
        (case (gic-dag-lookup $env $root-id)
          (((FoundDagValue $root-goal) (== $root-goal $goal))
           ($_ False))))
      ($_ False))))

(= (gic-check-dag $language $goal $root-id $nodes)
   (if (gic-language-valid $language)
     (case $language
       (((GInferenceLanguageV1
            $version $constructors $judgments $rules $conversion)
          (gic-check-dag-valid $rules $goal $root-id $nodes))
        ($_ False)))
     False))

(= (gic-check-dag-root-expected $env $check)
   (case $check
     (((GDagRootCheck $goal $root-id True)
        (case (gic-dag-lookup $env $root-id)
          (((FoundDagValue $root-goal) (== $root-goal $goal))
           ($_ False))))
      ((GDagRootCheck $goal $root-id False)
        (case (gic-dag-lookup $env $root-id)
          (((FoundDagValue $root-goal)
            (if (== $root-goal $goal) False True))
           ($_ True))))
      ($_ False))))

(= (gic-check-dag-roots $env $checks)
   (case $checks
     ((DagCheckNil True)
      ((DagCheckCons $check $rest)
        (if (gic-check-dag-root-expected $env $check)
          (gic-check-dag-roots $env $rest)
          False))
      ($_ False))))

(= (gic-check-dag-batch-valid $rules $nodes $checks)
   (case (gic-check-dag-nodes $rules $nodes DEnvNil)
     (((DagOK $env) (gic-check-dag-roots $env $checks))
      ($_ False))))

(= (gic-check-dag-batch $language $nodes $checks)
   (if (gic-language-valid $language)
     (case $language
       (((GInferenceLanguageV1
            $version $constructors $judgments $rules $conversion)
          (gic-check-dag-batch-valid $rules $nodes $checks))
        ($_ False)))
     False))

; ---------- Streaming stack/heap witness checking --------------------------
(= (gic-reverse-onto LNil $accumulator) $accumulator)
(= (gic-reverse-onto (LCons $head $tail) $accumulator)
   (gic-reverse-onto $tail (LCons $head $accumulator)))
(= (gic-reverse $values) (gic-reverse-onto $values LNil))

(= (gic-trace-consume $premises $stack)
   (case (GICTraceConsumePair $premises $stack)
     (((GICTraceConsumePair LNil $rest) (TraceStackOK $rest))
      ((GICTraceConsumePair
         (LCons $premise $more-premises)
         (TsCons $goal $more-stack))
        (if (== $premise $goal)
          (gic-trace-consume $more-premises $more-stack)
          TraceStackFail))
      ($_ TraceStackFail))))

(= (gic-trace-heap-snoc ThNil $goal) (ThCons $goal ThNil))
(= (gic-trace-heap-snoc (ThCons $head $tail) $goal)
   (ThCons $head (gic-trace-heap-snoc $tail $goal)))

(= (gic-trace-heap-get ThNil $index) NoTraceValue)
(= (gic-trace-heap-get (ThCons $head $tail) $index)
   (if (== $index 0)
     (FoundTraceValue $head)
     (gic-trace-heap-get $tail (- $index 1))))

(= (gic-trace-step $rules $state $action)
   (case (GICTraceStepPair $state $action)
     (((GICTraceStepPair
         (GTraceState $stack $heap) (GApply $rule-instance))
        (case (gic-instantiate-rule $rules $rule-instance)
          (((RuleOK $premises $conclusion)
            (case (gic-trace-consume (gic-reverse $premises) $stack)
              (((TraceStackOK $rest)
                (TraceStepOK
                  (GTraceState (TsCons $conclusion $rest) $heap)))
               ($_ TraceStepFail))))
           ($_ TraceStepFail))))
      ((GICTraceStepPair
         (GTraceState (TsCons $goal $rest) $heap) GSave)
        (TraceStepOK
          (GTraceState (TsCons $goal $rest)
            (gic-trace-heap-snoc $heap $goal))))
      ((GICTraceStepPair
         (GTraceState $stack $heap) (GRef $index))
        (case (gic-trace-heap-get $heap $index)
          (((FoundTraceValue $goal)
            (TraceStepOK (GTraceState (TsCons $goal $stack) $heap)))
           ($_ TraceStepFail))))
      ($_ TraceStepFail))))

(= (gic-run-trace $rules GaNil $state) (TraceOK $state))
(= (gic-run-trace $rules (GaCons $action $actions) $state)
   (case (gic-trace-step $rules $state $action)
     (((TraceStepOK $next-state)
        (gic-run-trace $rules $actions $next-state))
      ($_ TraceFail))))

(= (gic-check-trace-valid $rules $goal $actions)
   (case (gic-run-trace $rules $actions (GTraceState TsNil ThNil))
     (((TraceOK (GTraceState (TsCons $result TsNil) $heap))
        (== $result $goal))
      ($_ False))))

(= (gic-check-trace $language $goal $actions)
   (if (gic-language-valid $language)
     (case $language
       (((GInferenceLanguageV1
            $version $constructors $judgments $rules $conversion)
          (gic-check-trace-valid $rules $goal $actions))
        ($_ False)))
     False))

(= (gic-check-trace-expected $rules $check)
   (case $check
     (((GTraceCheck $goal $actions True)
        (gic-check-trace-valid $rules $goal $actions))
      ((GTraceCheck $goal $actions False)
        (if (gic-check-trace-valid $rules $goal $actions) False True))
      ($_ False))))

(= (gic-check-trace-checks $rules $checks)
   (case $checks
     ((TraceCheckNil True)
      ((TraceCheckCons $check $rest)
        (if (gic-check-trace-expected $rules $check)
          (gic-check-trace-checks $rules $rest)
          False))
      ($_ False))))

(= (gic-check-trace-batch $language $checks)
   (if (gic-language-valid $language)
     (case $language
       (((GInferenceLanguageV1
            $version $constructors $judgments $rules $conversion)
          (gic-check-trace-checks $rules $checks))
        ($_ False)))
     False))

; ---------- CeTTa indexed admission and trace execution --------------------
(: gic-index-load-constructor-step (-> Atom Bool Atom Bool))
(: gic-index-load-constructors (-> Atom Atom Bool))
(: gic-index-load-judgment-step (-> Atom Bool Atom Bool))
(: gic-index-load-judgments (-> Atom Atom Bool))
(: gic-index-load-rule-step (-> Atom Bool Atom Bool))
(: gic-index-load-rules (-> Atom Atom Bool))

(= (gic-index-has-constructor $space $head $arity)
   (_minimal-space-contains-exact
     $space (GICIndexedConstructor $head $arity)))

(= (gic-index-has-judgment $space $head $arity)
   (_minimal-space-contains-exact
     $space (GICIndexedJudgment $head $arity)))

(= (gic-index-fixed-list-valid $space LNil) True)
(= (gic-index-fixed-list-valid $space (LCons $pattern $rest))
   (if (gic-index-fixed-valid $space $pattern)
     (gic-index-fixed-list-valid $space $rest)
     False))

(= (gic-index-fixed-valid $space $pattern)
   (case $pattern
     (((Var $index) True)
      ((FVar $name) True)
      ((PApp $head $arguments)
        (if (gic-index-has-constructor
              $space $head (gic-list-length $arguments))
          (gic-index-fixed-list-valid $space $arguments)
          False))
      ((PLam $binder $body) (gic-index-fixed-valid $space $body))
      ((PMultiLam $arity $binders $body)
        (gic-index-fixed-valid $space $body))
      ((PSubst $body $replacement)
        (if (gic-index-fixed-valid $space $body)
          (gic-index-fixed-valid $space $replacement)
          False))
      ((PCollection $kind $elements $rest)
        (gic-index-fixed-list-valid $space $elements))
      ($_ False))))

(= (gic-index-judgment-valid $space $pattern)
   (case $pattern
     (((PApp $head $arguments)
        (if (gic-index-has-judgment
              $space $head (gic-list-length $arguments))
          (gic-index-fixed-list-valid $space $arguments)
          False))
      ($_ False))))

(= (gic-index-judgment-list-valid $space LNil) True)
(= (gic-index-judgment-list-valid $space (LCons $pattern $rest))
   (if (gic-index-judgment-valid $space $pattern)
     (gic-index-judgment-list-valid $space $rest)
     False))

(= (gic-index-rule-valid $space
      (GRuleV1 $id $formals $premises $conclusion $side-conditions))
   (let $patterns (gic-append $premises (LCons $conclusion LNil))
     (let $occurrences (gic-occurrences-list-at 0 $patterns)
       (if (== $id "") False
         (if (gic-nonempty-formal-names $formals)
           (if (gic-no-duplicates (gic-formal-names $formals))
             (if (gic-all-members $occurrences $formals)
               (if (gic-all-members $formals $occurrences)
                 (if (gic-pattern-list-valid $patterns)
                   (if (gic-index-judgment-list-valid $space $patterns)
                     (gic-side-conditions-valid $formals $side-conditions)
                     False)
                   False)
                 False)
               False)
             False)
           False)))))

(= (gic-index-load-constructor-step $space $valid $declaration)
   (if $valid
     (case $declaration
       (((CDecl $head $arity)
         (if (== $head "") False
           (if (_minimal-space-contains-exact
                 $space (GICIndexedConstructorKey $head))
             False
             (let $key-added
               (add-atom $space (GICIndexedConstructorKey $head))
               (let $declaration-added
                 (add-atom $space (GICIndexedConstructor $head $arity))
                 True)))))
        ($_ False)))
     False))

(= (gic-index-load-constructors $space $constructors)
   (case
     (chain (context-space) $fold-space
       (eval
         (_minimal-foldl-llist $constructors True $valid $declaration
           (gic-index-load-constructor-step $space $valid $declaration)
           $fold-space)))
     (((return $result) $result)
      ($_ False))))

(= (gic-index-load-judgment-step $space $valid $declaration)
   (if $valid
     (case $declaration
       (((JDecl $head $arity)
         (if (== $head "") False
           (if (gic-member $head
                 (LCons "$zip" (LCons "$map" (LCons "$eval" LNil))))
             False
             (if (_minimal-space-contains-exact
                   $space (GICIndexedConstructorKey $head))
               False
               (if (_minimal-space-contains-exact
                     $space (GICIndexedJudgmentKey $head))
                 False
                 (let $key-added
                   (add-atom $space (GICIndexedJudgmentKey $head))
                   (let $declaration-added
                     (add-atom $space
                       (GICIndexedJudgment $head $arity))
                     True)))))))
        ($_ False)))
     False))

(= (gic-index-load-judgments $space $judgments)
   (case
     (chain (context-space) $fold-space
       (eval
         (_minimal-foldl-llist $judgments True $valid $declaration
           (gic-index-load-judgment-step $space $valid $declaration)
           $fold-space)))
     (((return $result) $result)
      ($_ False))))

(= (gic-index-load-rule-step $space $valid $rule)
   (if $valid
     (case $rule
       (((GRuleV1
            $id $formals $premises $conclusion $side-conditions)
         (if (_minimal-space-contains-exact
               $space (GICIndexedRuleKey $id))
           False
           (if (gic-index-rule-valid $space $rule)
             (let $key-added
               (add-atom $space (GICIndexedRuleKey $id))
               (let $rule-added
                 (add-atom $space
                   (GICIndexedRule
                     $id $formals $premises $conclusion $side-conditions))
                 True))
             False)))
        ($_ False)))
     False))

(= (gic-index-load-rules $space $rules)
   (case
     (chain (context-space) $fold-space
       (eval
         (_minimal-foldl-llist $rules True $valid $rule
           (gic-index-load-rule-step $space $valid $rule)
           $fold-space)))
     (((return $result) $result)
      ($_ False))))

; The language is destructured exactly once at the public boundary.  Passing a
; large serialized language through a second helper duplicates a deeply nested
; value in the evaluator before its stack-safe row folds can begin.  The field
; helper retains the whole-language admission invariant while letting each row
; family flow directly into its indexed fold.
(: gic-build-index-fields-in
   (-> Atom Atom Atom Atom Atom Atom %Undefined%))

(= (gic-build-index-fields-in
      $space $version $constructors $judgments $rules $conversion)
   (if (== $version 1)
     (if (gic-conversion-valid $judgments $conversion)
       (if (gic-index-load-constructors $space $constructors)
         (if (gic-index-load-judgments $space $judgments)
           (if (gic-index-load-rules $space $rules)
             (GICIndexOK $space)
             GICIndexFail)
           GICIndexFail)
         GICIndexFail)
       GICIndexFail)
     GICIndexFail))

(= (gic-build-index $language)
   (case $language
     (((GInferenceLanguageV1
          $version $constructors $judgments $rules $conversion)
        (let $space (new-space)
          (gic-build-index-fields-in
            $space $version $constructors $judgments $rules $conversion)))
      ($_ GICIndexFail))))

(= (gic-build-pathmap-index $language)
   (case $language
     (((GInferenceLanguageV1
          $version $constructors $judgments $rules $conversion)
        (let $space (new-space pathmap)
          (gic-build-index-fields-in
            $space $version $constructors $judgments $rules $conversion)))
      ($_ GICIndexFail))))

(= (gic-index-lookup-rule $space $id)
   (case (collapse
           (match $space
             (GICIndexedRule
               $id $formals $premises $conclusion $side-conditions)
             (GRuleV1
               $id $formals $premises $conclusion $side-conditions)))
     ((($rule) (FoundRule $rule))
      ($_ NoRule))))

(= (gic-index-instantiate-rule $space (GRuleInst $id $arguments))
   (case (gic-index-lookup-rule $space $id)
     (((FoundRule
          (GRuleV1
            $found-id $formals $premises $conclusion $side-conditions))
        (if (gic-index-arguments-valid $space $formals $arguments)
          (if (gic-side-conditions-hold $arguments $side-conditions)
            (case (gic-instantiate-list $formals $arguments 0 $premises)
              (((PatternsOK $premise-results)
                (case (gic-instantiate
                        $formals $arguments 0 $conclusion)
                  (((PatternOK $conclusion-result)
                    (RuleOK $premise-results $conclusion-result))
                   ($_ RuleFail))))
               ($_ RuleFail)))
            RuleFail)
          RuleFail))
      ($_ RuleFail))))

; Indexed proof-DAG checking retains the same chronological child discipline
; as gic-check-dag while indexing both rules and admitted DAG values.
(= (gic-index-dag-lookup $space $id)
   (case (collapse
           (match $space (GICIndexedDagValue $id $goal) $goal))
     ((($only) (FoundDagValue $only))
      ($_ NoDagValue))))

; Retain the exact accepted node beside its derived conclusion.  Consumers
; can thereby reconstruct data from the same native proof object that passed
; checking instead of accepting an unrelated caller-supplied payload.
(= (gic-index-dag-node-lookup $space $id)
   (case (collapse
           (match $space
             (GICIndexedDagNode $id $rule-instance $child-ids)
             (FoundDagNode $rule-instance $child-ids)))
     ((($only) $only)
      ($_ NoDagNode))))

(= (gic-index-dag-children-match $space $premises $child-ids)
   (case (GICDagChildrenPair $premises $child-ids)
     (((GICDagChildrenPair LNil DrNil) True)
      ((GICDagChildrenPair
         (LCons $premise $more-premises)
         (DrCons $child-id $more-child-ids))
        (case (gic-index-dag-lookup $space $child-id)
          (((FoundDagValue $child-goal)
            (if (== $child-goal $premise)
              (gic-index-dag-children-match
                $space $more-premises $more-child-ids)
              False))
           ($_ False))))
      ($_ False))))

(= (gic-index-check-dag-nodes $space DnNil) DagOK)
(= (gic-index-check-dag-nodes $space
      (DnCons (GDNode $id $rule-instance $child-ids) $nodes))
   (case (gic-index-dag-lookup $space $id)
     ((NoDagValue
        (case (gic-index-instantiate-rule $space $rule-instance)
          (((RuleOK $premises $conclusion)
            (if (gic-index-dag-children-match $space $premises $child-ids)
              (let $added
                (add-atom $space (GICIndexedDagValue $id $conclusion))
                (let $added-node
                  (add-atom $space
                    (GICIndexedDagNode $id $rule-instance $child-ids))
                  (gic-index-check-dag-nodes $space $nodes)))
              DagFail))
           ($_ DagFail))))
      ($_ DagFail))))

(= (gic-index-check-dag-valid $space $goal $root-id $nodes)
   (case (gic-index-check-dag-nodes $space $nodes)
     ((DagOK
        (case (gic-index-dag-lookup $space $root-id)
          (((FoundDagValue $root-goal) (== $root-goal $goal))
           ($_ False))))
      ($_ False))))

; Stack-safe chronological DAG checking.  The grounded fold is only an
; iterator over ordinary GDNode proof terms; this step performs the same rule
; instantiation, ordered-premise comparison, duplicate-id rejection, and
; conclusion insertion as gic-index-check-dag-nodes.
(= (gic-index-check-dag-list-step $space $valid $node)
   (if $valid
     (case $node
       (((GDNode $id $rule-instance $child-ids)
         (case (gic-index-dag-lookup $space $id)
           ((NoDagValue
             (case (gic-index-instantiate-rule $space $rule-instance)
               (((RuleOK $premises $conclusion)
                 (if (gic-index-dag-children-match
                       $space $premises $child-ids)
                   (let $added
                     (add-atom $space
                       (GICIndexedDagValue $id $conclusion))
                     (let $added-node
                       (add-atom $space
                         (GICIndexedDagNode $id $rule-instance $child-ids))
                       True))
                   False))
                ($_ False))))
            ($_ False))))
        ($_ False)))
     False))

(= (gic-index-check-dag-list $space $nodes)
   (case
     (chain (context-space) $fold-space
       (eval
         (_minimal-foldl-llist $nodes True $valid $node
           (gic-index-check-dag-list-step $space $valid $node)
           $fold-space)))
     (((return $result) $result)
      ($_ False))))

(= (gic-index-check-dag-list-valid $space $goal $root-id $nodes)
   (if (gic-index-check-dag-list $space $nodes)
     (case (gic-index-dag-lookup $space $root-id)
       (((FoundDagValue $root-goal) (== $root-goal $goal))
       ($_ False)))
     False))

; Bounded node blocks are a transport representation of one chronological
; proof DAG.  Every node still passes through gic-index-check-dag-list-step,
; and the same index carries derived conclusions across block boundaries.
(= (gic-index-check-dag-block-step $space $valid $nodes)
   (if $valid (gic-index-check-dag-list $space $nodes) False))

(= (gic-index-check-dag-blocks $space $blocks)
   (case
     (chain (context-space) $fold-space
       (eval
         (_minimal-foldl-llist $blocks True $valid $nodes
           (gic-index-check-dag-block-step $space $valid $nodes)
           $fold-space)))
     (((return $result) $result)
      ($_ False))))

(= (gic-index-check-dag-blocks-valid $space $goal $root-id $blocks)
   (if (gic-index-check-dag-blocks $space $blocks)
     (case (gic-index-dag-lookup $space $root-id)
       (((FoundDagValue $root-goal) (== $root-goal $goal))
        ($_ False)))
     False))

(= (gic-check-dag-indexed $language $goal $root-id $nodes)
   (case (gic-build-index $language)
     (((GICIndexOK $space)
        (gic-index-check-dag-valid $space $goal $root-id $nodes))
      ($_ False))))

; Chunked DAG checking bounds serialized-list and traversal depth while the
; atomspace retains chronological values between chunks.
(= (gic-index-check-dag-chunks $space DcNil) DagOK)
(= (gic-index-check-dag-chunks $space (DcCons $nodes $chunks))
   (case (gic-index-check-dag-nodes $space $nodes)
     ((DagOK (gic-index-check-dag-chunks $space $chunks))
      ($_ DagFail))))

(= (gic-index-check-dag-chunks-valid $space $goal $root-id $chunks)
   (case (gic-index-check-dag-chunks $space $chunks)
     ((DagOK
        (case (gic-index-dag-lookup $space $root-id)
          (((FoundDagValue $root-goal) (== $root-goal $goal))
           ($_ False))))
      ($_ False))))

(= (gic-check-dag-chunks-indexed $language $goal $root-id $chunks)
   (case (gic-build-index $language)
     (((GICIndexOK $space)
        (gic-index-check-dag-chunks-valid $space $goal $root-id $chunks))
      ($_ False))))

; Streaming chronological DAG checking.  Each GSLiveNode carries releases
; performed only after its ordinary rule instance and ordered premises pass.
; Consecutive identifiers prevent a released identifier from being reused,
; while a premature release causes any later child lookup to fail.
(= (gic-index-release-dag-one $space $id)
   (case (gic-index-dag-lookup $space $id)
     (((FoundDagValue $goal)
        (let $removed-value
          (remove-atom $space
            (GICIndexedDagValue $id $goal))
          GICReleaseOK))
      ($_ GICReleaseFail))))

(= (gic-index-release-dag-many $space DrNil) GICReleaseOK)
(= (gic-index-release-dag-many $space (DrCons $id $ids))
   (case (gic-index-release-dag-one $space $id)
     ((GICReleaseOK (gic-index-release-dag-many $space $ids))
      ($_ GICReleaseFail))))

(= (gic-index-check-stream-nodes $space $expected DsnNil)
   (GICStreamOK $expected))
(= (gic-index-check-stream-nodes $space $expected
      (DsnCons
        (GSLiveNode
          (GDNode $id $rule-instance $child-ids) $releases)
        $nodes))
   (if (== $id $expected)
     (case (gic-index-dag-lookup $space $id)
       ((NoDagValue
          (case (gic-index-instantiate-rule $space $rule-instance)
            (((RuleOK $premises $conclusion)
              (if
                (gic-index-dag-children-match
                  $space $premises $child-ids)
                (let $added
                  (add-atom $space
                    (GICIndexedDagValue $id $conclusion))
                  (case
                    (gic-index-release-dag-many
                      $space $releases)
                    ((GICReleaseOK
                       (gic-index-check-stream-nodes
                         $space (+ $expected 1) $nodes))
                     ($_ (GICStreamFail)))))
                (GICStreamFail)))
             ($_ (GICStreamFail)))))
        ($_ (GICStreamFail))))
     (GICStreamFail)))

(= (gic-index-check-stream-chunks $space $expected DscNil)
   (GICStreamOK $expected))
(= (gic-index-check-stream-chunks $space $expected
      (DscCons $nodes $chunks))
   (case (gic-index-check-stream-nodes $space $expected $nodes)
     (((GICStreamOK $next)
       (gic-index-check-stream-chunks $space $next $chunks))
      ($_ (GICStreamFail)))))

(= (gic-index-check-stream-chunks-valid
      $space $goal $root-id $chunks)
   (case (gic-index-check-stream-chunks $space 0 $chunks)
     (((GICStreamOK $next)
       (case (gic-index-dag-lookup $space $root-id)
         (((FoundDagValue $root-goal) (== $root-goal $goal))
          ($_ False))))
      ($_ False))))

(= (gic-check-dag-streaming-indexed
      $language $goal $root-id $chunks)
   (case (gic-build-index $language)
     (((GICIndexOK $space)
       (gic-index-check-stream-chunks-valid
         $space $goal $root-id $chunks))
      ($_ False))))

; Explicit-state streaming is the process-boundary form of the same
; chronological checker.  Unlike the atomspace implementation above, its
; live conclusions are ordinary data and can therefore be serialized between
; bounded worker processes.  The caller must begin with expected id zero and
; the empty environment; every successful step returns the only next state.
(= (gic-pure-release-dag-one DEnvNil $target) GICPureReleaseFail)
(= (gic-pure-release-dag-one
      (DEnvCons (DVal $id $goal) $rest) $target)
   (if (== $id $target)
     (GICPureReleaseOK $rest)
     (case (gic-pure-release-dag-one $rest $target)
       (((GICPureReleaseOK $new-rest)
         (GICPureReleaseOK
           (DEnvCons (DVal $id $goal) $new-rest)))
        ($_ GICPureReleaseFail)))))

(= (gic-pure-release-dag-many $env DrNil)
   (GICPureReleaseOK $env))
(= (gic-pure-release-dag-many
      $env (DrCons $id $ids))
   (case (gic-pure-release-dag-one $env $id)
     (((GICPureReleaseOK $next-env)
       (gic-pure-release-dag-many $next-env $ids))
      ($_ GICPureReleaseFail))))

(= (gic-pure-check-stream-nodes
      $rules $expected $env DsnNil)
   (GICPureStreamOK
     (GICPureStreamState $expected $env)))
(= (gic-pure-check-stream-nodes
      $rules $expected $env
      (DsnCons
        (GSLiveNode
          (GDNode $id $rule-instance $child-ids) $releases)
        $nodes))
   (if (== $id $expected)
     (case (gic-dag-lookup $env $id)
       ((NoDagValue
          (case (gic-instantiate-rule $rules $rule-instance)
            (((RuleOK $premises $conclusion)
              (if
                (gic-dag-children-match
                  $env $premises $child-ids)
                (case
                  (gic-pure-release-dag-many
                    (DEnvCons
                      (DVal $id $conclusion) $env)
                    $releases)
                  (((GICPureReleaseOK $next-env)
                    (gic-pure-check-stream-nodes
                      $rules (+ $expected 1) $next-env $nodes))
                   ($_ GICPureStreamFail)))
                GICPureStreamFail))
             ($_ GICPureStreamFail))))
        ($_ GICPureStreamFail)))
     GICPureStreamFail))

(= (gic-pure-check-stream-chunks
      $rules $state DscNil)
   (GICPureStreamOK $state))
(= (gic-pure-check-stream-chunks
      $rules $state (DscCons $nodes $chunks))
   (case $state
     (((GICPureStreamState $expected $env)
       (case
         (gic-pure-check-stream-nodes
           $rules $expected $env $nodes)
         (((GICPureStreamOK $next-state)
           (gic-pure-check-stream-chunks
             $rules $next-state $chunks))
          ($_ GICPureStreamFail))))
      ($_ GICPureStreamFail))))

; Execute one externally bounded chunk and return its serializable state.
(= (gic-check-dag-pure-stream-step
      $language $state $nodes)
   (if (gic-language-valid $language)
     (case $language
       (((GInferenceLanguageV1
            $version $constructors $judgments $rules $conversion)
         (case $state
           (((GICPureStreamState $expected $env)
             (gic-pure-check-stream-nodes
               $rules $expected $env $nodes))
            ($_ GICPureStreamFail))))
        ($_ GICPureStreamFail)))
     GICPureStreamFail))

(= (gic-finish-dag-pure-stream $state $goal $root-id)
   (case $state
     (((GICPureStreamState $expected $env)
       (case (gic-dag-lookup $env $root-id)
         (((FoundDagValue $root-goal) (== $root-goal $goal))
          ($_ False))))
      ($_ False))))

(= (gic-check-dag-pure-streaming
      $language $goal $root-id $chunks)
   (if (gic-language-valid $language)
     (case $language
       (((GInferenceLanguageV1
            $version $constructors $judgments $rules $conversion)
         (case
           (gic-pure-check-stream-chunks
             $rules
             (GICPureStreamState 0 DEnvNil)
             $chunks)
           (((GICPureStreamOK $state)
             (gic-finish-dag-pure-stream
               $state $goal $root-id))
            ($_ False))))
        ($_ False)))
     False))

; Check a terminal node against an already admitted chronological prefix
; without inserting it, allowing several adversarial variants to share one
; indexed prefix.
(= (gic-index-check-dag-terminal $space $goal
      (GDNode $id $rule-instance $child-ids))
   (case (gic-index-dag-lookup $space $id)
     ((NoDagValue
        (case (gic-index-instantiate-rule $space $rule-instance)
          (((RuleOK $premises $conclusion)
            (if (gic-index-dag-children-match $space $premises $child-ids)
              (== $conclusion $goal)
              False))
           ($_ False))))
      ($_ False))))

(= (gic-check-dag-terminal-indexed
      $language $goal $prefix-chunks $terminal)
   (case (gic-build-index $language)
     (((GICIndexOK $space)
        (case (gic-index-check-dag-chunks $space $prefix-chunks)
          ((DagOK (gic-index-check-dag-terminal $space $goal $terminal))
           ($_ False))))
      ($_ False))))

(= (gic-index-trace-step $space $state $action)
   (case $action
     (((GApply $rule-instance)
        (case (gic-index-instantiate-rule $space $rule-instance)
          (((RuleOK $premises $conclusion)
            (case $state
              (((GTraceState $stack $heap)
                (case (gic-trace-consume
                        (gic-reverse $premises) $stack)
                  (((TraceStackOK $rest)
                    (TraceStepOK
                      (GTraceState (TsCons $conclusion $rest) $heap)))
                   ($_ TraceStepFail))))
               ($_ TraceStepFail))))
           ($_ TraceStepFail))))
      (GSave (gic-trace-step LNil $state GSave))
      ((GRef $index) (gic-trace-step LNil $state (GRef $index)))
      ($_ TraceStepFail))))

(= (gic-index-run-trace $space GaNil $state) (TraceOK $state))
(= (gic-index-run-trace $space (GaCons $action $actions) $state)
   (case (gic-index-trace-step $space $state $action)
     (((TraceStepOK $next-state)
        (gic-index-run-trace $space $actions $next-state))
      ($_ TraceFail))))

(= (gic-index-check-trace $space $goal $actions)
   (case (gic-index-run-trace
           $space $actions (GTraceState TsNil ThNil))
     (((TraceOK (GTraceState (TsCons $result TsNil) $heap))
        (== $result $goal))
      ($_ False))))

(= (gic-index-check-expected $space $check)
   (case $check
     (((GTraceCheck $goal $actions True)
        (gic-index-check-trace $space $goal $actions))
      ((GTraceCheck $goal $actions False)
        (if (gic-index-check-trace $space $goal $actions) False True))
      ($_ False))))

(= (gic-index-checks $space $checks)
   (case $checks
     ((TraceCheckNil True)
      ((TraceCheckCons $check $rest)
        (if (gic-index-check-expected $space $check)
          (gic-index-checks $space $rest)
          False))
      ($_ False))))

(= (gic-check-trace-indexed $language $checks)
   (case (gic-build-index $language)
     (((GICIndexOK $space) (gic-index-checks $space $checks))
      ($_ False))))

(= (gic-check-trace-pathmap $language $checks)
   (case (gic-build-pathmap-index $language)
     (((GICIndexOK $space) (gic-index-checks $space $checks))
      ($_ False))))

; ---------- Executable teeth ------------------------------------------------
(= (gic-A) (PApp "A" LNil))
(= (gic-B) (PApp "B" LNil))
(= (gic-imp $left $right)
   (PApp "Imp" (LCons $left (LCons $right LNil))))
(= (gic-proves $term) (PApp "Proves" (LCons $term LNil)))
(= (gic-substitutes $body $replacement $result)
   (PApp "Substitutes"
     (LCons (PLam BNone $body)
       (LCons $replacement (LCons $result LNil)))))
(= (gic-drops-unused $body $result)
   (PApp "DropsUnused"
     (LCons (PLam BNone $body) (LCons $result LNil))))

(= (gic-constructors)
   (LCons (CDecl "A" 0)
     (LCons (CDecl "B" 0)
       (LCons (CDecl "Imp" 2) LNil))))
(= (gic-judgments)
   (LCons (JDecl "Proves" 1)
     (LCons (JDecl "Substitutes" 3)
       (LCons (JDecl "DropsUnused" 2)
         (LCons (JDecl "Converts" 2) LNil)))))

(= (gic-ax-a)
   (GRuleV1 "ax-a" LNil LNil (gic-proves (gic-A)) LNil))
(= (gic-ax-imp-ab)
   (GRuleV1 "ax-imp-ab" LNil LNil
     (gic-proves (gic-imp (gic-A) (gic-B))) LNil))
(= (gic-mp)
   (GRuleV1 "mp"
     (LCons (Formal "p" 0) (LCons (Formal "q" 0) LNil))
     (LCons (gic-proves (FVar "p"))
       (LCons (gic-proves (gic-imp (FVar "p") (FVar "q"))) LNil))
     (gic-proves (FVar "q"))
     LNil))
(= (gic-lam)
   (GRuleV1 "lam"
     (LCons (Formal "body" 1) LNil)
     LNil
     (gic-proves (PLam BNone (FVar "body")))
     LNil))
(= (gic-subst)
   (GRuleV1 "subst"
     (LCons (Formal "body" 1)
       (LCons (Formal "replacement" 0) LNil))
     LNil
     (gic-proves (PSubst (FVar "body") (FVar "replacement")))
     LNil))
(= (gic-join-a)
   (GRuleV1 "join-a" LNil
     (LCons (gic-proves (gic-A))
       (LCons (gic-proves (gic-A)) LNil))
     (gic-proves (gic-A))
     LNil))
(= (gic-explicit-substitution)
   (GRuleV1 "explicit-substitution"
     (LCons (Formal "body" 1)
       (LCons (Formal "replacement" 0)
         (LCons (Formal "result" 0) LNil)))
     LNil
     (gic-substitutes
       (FVar "body") (FVar "replacement") (FVar "result"))
     (LCons (GExplicitSubstitution 0 0 1 2) LNil)))
(= (gic-unused-binder-elimination)
   (GRuleV1 "unused-binder-elimination"
     (LCons (Formal "body" 1)
       (LCons (Formal "result" 0) LNil))
     LNil
     (gic-drops-unused (FVar "body") (FVar "result"))
     (LCons (GUnusedBinderElimination 0 0 1) LNil)))
(= (gic-invalid-side-condition-rule)
   (GRuleV1 "invalid-side-condition"
     (LCons (Formal "body" 1)
       (LCons (Formal "replacement" 0)
         (LCons (Formal "result" 0) LNil)))
     LNil
     (gic-substitutes
       (FVar "body") (FVar "replacement") (FVar "result"))
     (LCons (GExplicitSubstitution 0 1 0 2) LNil)))

(= (gic-rules)
   (LCons (gic-ax-a)
     (LCons (gic-ax-imp-ab)
       (LCons (gic-mp)
         (LCons (gic-lam)
           (LCons (gic-subst)
             (LCons (gic-join-a)
               (LCons (gic-explicit-substitution)
                 (LCons (gic-unused-binder-elimination) LNil)))))))))
(= (gic-language)
   (GInferenceLanguageV1
     1 (gic-constructors) (gic-judgments) (gic-rules) GNoConversion))

(= (gic-proof-a) (GProof (GRuleInst "ax-a" LNil) PrNil))
(= (gic-proof-imp-ab) (GProof (GRuleInst "ax-imp-ab" LNil) PrNil))
(= (gic-proof-b)
   (GProof
     (GRuleInst "mp" (LCons (gic-A) (LCons (gic-B) LNil)))
     (PrCons (gic-proof-a) (PrCons (gic-proof-imp-ab) PrNil))))

!(assertEqual (gic-language-valid (gic-language)) True)
!(assertEqual (gic-check (gic-language) (gic-proves (gic-B)) (gic-proof-b)) True)
!(assertEqual
  (gic-check (gic-language) (gic-proves (gic-A)) (gic-proof-b))
  False)
!(assertEqual
  (gic-check (gic-language) (gic-proves (gic-B))
    (GProof
      (GRuleInst "mp" (LCons (gic-A) (LCons (gic-B) LNil)))
      (PrCons (gic-proof-imp-ab) (PrCons (gic-proof-a) PrNil))))
  False)
!(assertEqual
  (gic-check (gic-language) (gic-proves (gic-B))
    (GProof
      (GRuleInst "mp" (LCons (gic-A) (LCons (gic-B) LNil)))
      (PrCons (gic-proof-a) PrNil)))
  False)
!(assertEqual
  (gic-check (gic-language) (gic-proves (gic-B))
    (GProof
      (GRuleInst "mp" (LCons (gic-A) (LCons (gic-B) LNil)))
      (PrCons (gic-proof-a)
        (PrCons (gic-proof-imp-ab) (PrCons (gic-proof-a) PrNil)))))
  False)
!(assertEqual
  (gic-check (gic-language) (gic-proves (gic-B))
    (GProof (GRuleInst "missing-rule" LNil) PrNil))
  False)

; Exact-depth binder argument: Var 0 is closed relative to depth one.
!(assertEqual
  (gic-check (gic-language)
    (gic-proves (PLam BNone (Var 0)))
    (GProof (GRuleInst "lam" (LCons (Var 0) LNil)) PrNil))
  True)
!(assertEqual
  (gic-check (gic-language)
    (gic-proves (PLam BNone (Var 1)))
    (GProof (GRuleInst "lam" (LCons (Var 1) LNil)) PrNil))
  False)
!(assertEqual
  (gic-check (gic-language)
    (gic-proves (PLam BNone (PLam (BSome "x") (Var 0))))
    (GProof
      (GRuleInst "lam" (LCons (PLam (BSome "x") (Var 0)) LNil)) PrNil))
  False)

; Explicit substitution is transported as syntax; it is not evaluated here.
!(assertEqual
  (gic-check (gic-language)
    (gic-proves (PSubst (Var 0) (gic-A)))
    (GProof
      (GRuleInst "subst" (LCons (Var 0) (LCons (gic-A) LNil))) PrNil))
  True)

; Generic side conditions are executable parts of the same flat language.
!(assertEqual
  (gic-check (gic-language)
    (gic-substitutes (Var 0) (gic-A) (gic-A))
    (GProof
      (GRuleInst "explicit-substitution"
        (LCons (Var 0) (LCons (gic-A) (LCons (gic-A) LNil))))
      PrNil))
  True)
!(assertEqual
  (gic-check (gic-language)
    (gic-substitutes (Var 0) (gic-A) (gic-B))
    (GProof
      (GRuleInst "explicit-substitution"
        (LCons (Var 0) (LCons (gic-A) (LCons (gic-B) LNil))))
      PrNil))
  False)
!(assertEqual
  (gic-check (gic-language)
    (gic-drops-unused (gic-A) (gic-A))
    (GProof
      (GRuleInst "unused-binder-elimination"
        (LCons (gic-A) (LCons (gic-A) LNil)))
      PrNil))
  True)
!(assertEqual
  (gic-check (gic-language)
    (gic-drops-unused (Var 0) (gic-A))
    (GProof
      (GRuleInst "unused-binder-elimination"
        (LCons (Var 0) (LCons (gic-A) LNil)))
      PrNil))
  False)

; Admission negatives ensure malformed serialized languages cannot acquire
; validity merely because one rule lookup happens to succeed.
!(assertEqual
  (gic-language-valid
    (GInferenceLanguageV1 1 (gic-constructors) (gic-judgments)
      (LCons (gic-ax-a) (LCons (gic-ax-a) LNil)) GNoConversion))
  False)
!(assertEqual
  (gic-language-valid
    (GInferenceLanguageV1 1 (gic-constructors) (gic-judgments)
      (LCons
        (GRuleV1 "bad-depth" (LCons (Formal "x" 0) LNil) LNil
          (gic-proves (PLam BNone (FVar "x"))) LNil)
        LNil)
      GNoConversion))
  False)
!(assertEqual
  (gic-language-valid
    (GInferenceLanguageV1 1 (gic-constructors) (gic-judgments)
      (LCons
        (GRuleV1 "bad-rest" (LCons (Formal "x" 0) LNil) LNil
          (gic-proves (PCollection "Bag" LNil (RSome "x"))) LNil)
        LNil)
      GNoConversion))
  False)
!(assertEqual
  (gic-language-valid
    (GInferenceLanguageV1
      2 (gic-constructors) (gic-judgments) (gic-rules) GNoConversion))
  False)
!(assertEqual
  (gic-language-valid
    (GInferenceLanguageV1 1
      (gic-constructors) (gic-judgments) (gic-rules)
      (GConversion "Proves" "conversion-v1")))
  False)
!(assertEqual
  (gic-language-valid
    (GInferenceLanguageV1 1
      (gic-constructors) (gic-judgments) (gic-rules)
      (GConversion "Converts" "conversion-v1")))
  True)
!(assertEqual
  (gic-language-valid
    (GInferenceLanguageV1 1 (gic-constructors) (gic-judgments)
      (LCons (gic-invalid-side-condition-rule) LNil)
      GNoConversion))
  False)

; Batch admission validates the language once, then checks both the
; positive witness and its exact wrong-goal negative against the same rules.
!(assertEqual
  (gic-check-batch (gic-language)
    (CheckCons
      (GCheck (gic-proves (gic-B)) (gic-proof-b) True)
      (CheckCons
        (GCheck (gic-proves (gic-A)) (gic-proof-b) False)
        CheckNil)))
  True)

(= (gic-proof-dag)
   (DnCons (GDNode "a" (GRuleInst "ax-a" LNil) DrNil)
     (DnCons (GDNode "imp" (GRuleInst "ax-imp-ab" LNil) DrNil)
       (DnCons
         (GDNode "b"
           (GRuleInst "mp" (LCons (gic-A) (LCons (gic-B) LNil)))
           (DrCons "a" (DrCons "imp" DrNil)))
         DnNil))))

!(assertEqual
  (gic-check-dag (gic-language) (gic-proves (gic-B)) "b"
    (gic-proof-dag))
  True)
!(assertEqual
  (gic-check-dag (gic-language) (gic-proves (gic-B)) "b"
    (DnCons
      (GDNode "b"
        (GRuleInst "mp" (LCons (gic-A) (LCons (gic-B) LNil)))
        (DrCons "a" (DrCons "imp" DrNil)))
      (gic-proof-dag)))
  False)
!(assertEqual
  (gic-check-dag (gic-language) (gic-proves (gic-B)) "b"
    (DnCons (GDNode "a" (GRuleInst "ax-a" LNil) DrNil)
      (DnCons (GDNode "a" (GRuleInst "ax-imp-ab" LNil) DrNil) DnNil)))
  False)
!(assertEqual
  (gic-check-dag (gic-language) (gic-proves (gic-B)) "b"
    (DnCons (GDNode "a" (GRuleInst "ax-a" LNil) DrNil)
      (DnCons (GDNode "imp" (GRuleInst "ax-imp-ab" LNil) DrNil)
        (DnCons
          (GDNode "b"
            (GRuleInst "mp" (LCons (gic-A) (LCons (gic-B) LNil)))
            (DrCons "missing" (DrCons "imp" DrNil)))
          DnNil))))
  False)
!(assertEqual
  (gic-check-dag (gic-language) (gic-proves (gic-B)) "b"
    (DnCons (GDNode "a" (GRuleInst "ax-a" LNil) DrNil)
      (DnCons (GDNode "imp" (GRuleInst "ax-imp-ab" LNil) DrNil)
        (DnCons
          (GDNode "b"
            (GRuleInst "mp" (LCons (gic-A) (LCons (gic-B) LNil)))
            (DrCons "imp" (DrCons "a" DrNil)))
          DnNil))))
  False)
!(assertEqual
  (gic-check-dag-batch (gic-language) (gic-proof-dag)
    (DagCheckCons
      (GDagRootCheck (gic-proves (gic-B)) "b" True)
      (DagCheckCons
        (GDagRootCheck (gic-proves (gic-B)) "missing" False)
        DagCheckNil)))
  True)
!(assertEqual
  (gic-check-dag-indexed (gic-language) (gic-proves (gic-B)) "b"
    (gic-proof-dag))
  True)
!(assertEqual
  (gic-check-dag-indexed (gic-language) (gic-proves (gic-B)) "b"
    (DnCons (GDNode "a" (GRuleInst "ax-a" LNil) DrNil)
      (DnCons (GDNode "imp" (GRuleInst "ax-imp-ab" LNil) DrNil)
        (DnCons
          (GDNode "b"
            (GRuleInst "mp" (LCons (gic-A) (LCons (gic-B) LNil)))
            (DrCons "missing" (DrCons "imp" DrNil)))
          DnNil))))
  False)
(= (gic-proof-dag-chunks)
   (DcCons
     (DnCons (GDNode "a" (GRuleInst "ax-a" LNil) DrNil)
       (DnCons (GDNode "imp" (GRuleInst "ax-imp-ab" LNil) DrNil) DnNil))
     (DcCons
       (DnCons
         (GDNode "b"
           (GRuleInst "mp" (LCons (gic-A) (LCons (gic-B) LNil)))
           (DrCons "a" (DrCons "imp" DrNil)))
         DnNil)
       DcNil)))
!(assertEqual
  (gic-check-dag-chunks-indexed
    (gic-language) (gic-proves (gic-B)) "b"
    (gic-proof-dag-chunks))
  True)
!(assertEqual
  (gic-check-dag-chunks-indexed
    (gic-language) (gic-proves (gic-B)) "b"
    (DcCons
      (DnCons (GDNode "a" (GRuleInst "ax-a" LNil) DrNil)
        (DnCons (GDNode "imp" (GRuleInst "ax-imp-ab" LNil) DrNil) DnNil))
      (DcCons
        (DnCons
          (GDNode "b"
            (GRuleInst "mp" (LCons (gic-A) (LCons (gic-B) LNil)))
            (DrCons "missing" (DrCons "imp" DrNil)))
          DnNil)
        DcNil)))
  False)
(= (gic-proof-dag-streaming-chunks)
   (DscCons
     (DsnCons
       (GSLiveNode
         (GDNode 0 (GRuleInst "ax-a" LNil) DrNil)
         DrNil)
       (DsnCons
         (GSLiveNode
           (GDNode 1 (GRuleInst "ax-imp-ab" LNil) DrNil)
           DrNil)
         DsnNil))
     (DscCons
       (DsnCons
         (GSLiveNode
           (GDNode 2
             (GRuleInst "mp" (LCons (gic-A) (LCons (gic-B) LNil)))
             (DrCons 0 (DrCons 1 DrNil)))
           (DrCons 0 (DrCons 1 DrNil)))
         DsnNil)
       DscNil)))
!(assertEqual
  (gic-check-dag-streaming-indexed
    (gic-language) (gic-proves (gic-B)) 2
    (gic-proof-dag-streaming-chunks))
  True)
; A needed premise released after node zero is absent at node two.
!(assertEqual
  (gic-check-dag-streaming-indexed
    (gic-language) (gic-proves (gic-B)) 2
    (DscCons
      (DsnCons
        (GSLiveNode
          (GDNode 0 (GRuleInst "ax-a" LNil) DrNil)
          (DrCons 0 DrNil))
        (DsnCons
          (GSLiveNode
            (GDNode 1 (GRuleInst "ax-imp-ab" LNil) DrNil)
            DrNil)
          DsnNil))
      (DscCons
        (DsnCons
          (GSLiveNode
            (GDNode 2
              (GRuleInst "mp" (LCons (gic-A) (LCons (gic-B) LNil)))
              (DrCons 0 (DrCons 1 DrNil)))
            (DrCons 1 DrNil))
          DsnNil)
        DscNil)))
  False)
; Consecutive IDs reject reuse even after the old entry was released.
!(assertEqual
  (gic-check-dag-streaming-indexed
    (gic-language) (gic-proves (gic-B)) 2
    (DscCons
      (DsnCons
        (GSLiveNode
          (GDNode 0 (GRuleInst "ax-a" LNil) DrNil)
          (DrCons 0 DrNil))
        (DsnCons
          (GSLiveNode
            (GDNode 0 (GRuleInst "ax-imp-ab" LNil) DrNil)
            DrNil)
          DsnNil))
      DscNil))
  False)
; Unknown releases fail closed.
!(assertEqual
  (gic-check-dag-streaming-indexed
    (gic-language) (gic-proves (gic-A)) 0
    (DscCons
      (DsnCons
        (GSLiveNode
          (GDNode 0 (GRuleInst "ax-a" LNil) DrNil)
          (DrCons 99 DrNil))
        DsnNil)
      DscNil))
  False)
!(assertEqual
  (gic-check-dag-pure-streaming
    (gic-language) (gic-proves (gic-B)) 2
    (gic-proof-dag-streaming-chunks))
  True)
!(assertEqual
  (gic-check-dag-pure-stream-step
    (gic-language)
    (GICPureStreamState 0 DEnvNil)
    (DsnCons
      (GSLiveNode
        (GDNode 0 (GRuleInst "ax-a" LNil) DrNil)
        DrNil)
      (DsnCons
        (GSLiveNode
          (GDNode 1 (GRuleInst "ax-imp-ab" LNil) DrNil)
          DrNil)
        DsnNil)))
  (GICPureStreamOK
    (GICPureStreamState 2
      (DEnvCons
        (DVal 1 (gic-proves (gic-imp (gic-A) (gic-B))))
        (DEnvCons (DVal 0 (gic-proves (gic-A))) DEnvNil)))))
!(assertEqual
  (gic-check-dag-pure-streaming
    (gic-language) (gic-proves (gic-B)) 2
    (DscCons
      (DsnCons
        (GSLiveNode
          (GDNode 0 (GRuleInst "ax-a" LNil) DrNil)
          (DrCons 0 DrNil))
        (DsnCons
          (GSLiveNode
            (GDNode 1 (GRuleInst "ax-imp-ab" LNil) DrNil)
            DrNil)
          DsnNil))
      (DscCons
        (DsnCons
          (GSLiveNode
            (GDNode 2
              (GRuleInst "mp" (LCons (gic-A) (LCons (gic-B) LNil)))
              (DrCons 0 (DrCons 1 DrNil)))
            (DrCons 1 DrNil))
          DsnNil)
        DscNil)))
  False)
!(assertEqual
  (gic-check-dag-pure-streaming
    (gic-language) (gic-proves (gic-B)) 2
    (DscCons
      (DsnCons
        (GSLiveNode
          (GDNode 0 (GRuleInst "ax-a" LNil) DrNil)
          (DrCons 0 DrNil))
        (DsnCons
          (GSLiveNode
            (GDNode 0 (GRuleInst "ax-imp-ab" LNil) DrNil)
            DrNil)
          DsnNil))
      DscNil))
  False)
!(assertEqual
  (gic-check-dag-pure-streaming
    (gic-language) (gic-proves (gic-A)) 0
    (DscCons
      (DsnCons
        (GSLiveNode
          (GDNode 0 (GRuleInst "ax-a" LNil) DrNil)
          (DrCons 99 DrNil))
        DsnNil)
      DscNil))
  False)
!(assertEqual
  (gic-check-dag-terminal-indexed
    (gic-language) (gic-proves (gic-B))
    (DcCons
      (DnCons (GDNode "a" (GRuleInst "ax-a" LNil) DrNil)
        (DnCons (GDNode "imp" (GRuleInst "ax-imp-ab" LNil) DrNil) DnNil))
      DcNil)
    (GDNode "b"
      (GRuleInst "mp" (LCons (gic-A) (LCons (gic-B) LNil)))
      (DrCons "a" (DrCons "imp" DrNil))))
  True)
!(assertEqual
  (gic-check-dag-terminal-indexed
    (gic-language) (gic-proves (gic-B))
    (DcCons
      (DnCons (GDNode "a" (GRuleInst "ax-a" LNil) DrNil)
        (DnCons (GDNode "imp" (GRuleInst "ax-imp-ab" LNil) DrNil) DnNil))
      DcNil)
    (GDNode "b"
      (GRuleInst "mp" (LCons (gic-A) (LCons (gic-B) LNil)))
      (DrCons "missing" (DrCons "imp" DrNil))))
  False)

(= (gic-proof-b-trace)
   (GaCons (GApply (GRuleInst "ax-a" LNil))
     (GaCons (GApply (GRuleInst "ax-imp-ab" LNil))
       (GaCons
         (GApply
           (GRuleInst "mp" (LCons (gic-A) (LCons (gic-B) LNil))))
         GaNil))))
(= (gic-saved-a-trace)
   (GaCons (GApply (GRuleInst "ax-a" LNil))
     (GaCons GSave
       (GaCons (GRef 0)
         (GaCons (GApply (GRuleInst "join-a" LNil)) GaNil)))))

!(assertEqual
  (gic-check-trace (gic-language) (gic-proves (gic-B))
    (gic-proof-b-trace))
  True)
!(assertEqual
  (gic-check-trace (gic-language) (gic-proves (gic-A))
    (gic-saved-a-trace))
  True)
!(assertEqual
  (gic-check-trace (gic-language) (gic-proves (gic-A))
    (GaCons (GRef 0) GaNil))
  False)
!(assertEqual
  (gic-check-trace (gic-language) (gic-proves (gic-B))
    (GaCons
      (GApply (GRuleInst "mp" (LCons (gic-A) (LCons (gic-B) LNil))))
      GaNil))
  False)
!(assertEqual
  (gic-check-trace (gic-language) (gic-proves (gic-A))
    (GaCons (GApply (GRuleInst "ax-a" LNil))
      (GaCons (GApply (GRuleInst "ax-a" LNil)) GaNil)))
  False)
!(assertEqual
  (gic-check-trace-batch (gic-language)
    (TraceCheckCons
      (GTraceCheck (gic-proves (gic-B)) (gic-proof-b-trace) True)
      (TraceCheckCons
        (GTraceCheck (gic-proves (gic-A))
          (GaCons (GRef 0) GaNil) False)
        TraceCheckNil)))
  True)
!(assertEqual
  (gic-check-trace-indexed (gic-language)
    (TraceCheckCons
      (GTraceCheck (gic-proves (gic-B)) (gic-proof-b-trace) True)
      (TraceCheckCons
        (GTraceCheck (gic-proves (gic-A))
          (GaCons (GRef 0) GaNil) False)
        TraceCheckNil)))
  True)

!(GICSummary 51 51 0)
