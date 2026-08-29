; =============================================================================
; lib_parse_inference_v0.metta
;
; Grammar-derived, source-indexed proof checking for lib_parse.
;
; Classification: generic substrate.  Native SLR/GLR/GLL code is an
; untrusted proof producer.  This module derives a finite inference
; language from grammar data and a token ledger, lowers shared parser
; trees to ordinary GProof values, and delegates acceptance to the generic
; inference checker.
;
; The terminal/nonterminal fragment uses the same judgment vocabulary and
; rule serialization as GrammarInferenceExtraction.lean.  VarD/LexD leaves
; are represented by source-indexed ground rules in this operational v0;
; their reference correspondence theorem remains a separate obligation.
; =============================================================================

!(import! &self generic_inference_checker_v0)
!(import! &self gparse)
!(import! &self str)

; ---------- Private list and text helpers ----------------------------------
(= (lib_parse:append LNil $right) $right)
(= (lib_parse:append (LCons $head $tail) $right)
   (LCons $head (lib_parse:append $tail $right)))

(= (lib_parse:pr-append PrNil $right) $right)
(= (lib_parse:pr-append (PrCons $head $tail) $right)
   (PrCons $head (lib_parse:pr-append $tail $right)))

(= (lib_parse:atom-text $atom) (repr $atom))

(= (lib_parse:index-text $index) (repr $index))

(= (lib_parse:concat3 $first $second $third)
   (let $first-second (str:concat $first $second)
     (str:concat $first-second $third)))

(= (lib_parse:literal-label $kind $payload)
   (let $prefix (lib_parse:concat3 "__lib_parse.literal." $kind ".")
     (str:concat $prefix $payload)))

(= (lib_parse:rule-id $kind $payload)
   (let $length (str:length $payload)
     (let $length-text (lib_parse:index-text $length)
       (let $prefix (lib_parse:concat3 "__lib_parse.rule." $kind ".")
         (let $with-length (str:concat $prefix $length-text)
           (lib_parse:concat3 $with-length "." $payload))))))

(= (lib_parse:indexed-payload $source $index)
   (let $index-text (lib_parse:index-text $index)
     (lib_parse:concat3 $source ":" $index-text)))

(= (lib_parse:source-pattern $source)
   (PApp (lib_parse:literal-label "source" $source) LNil))

(= (lib_parse:token-pattern $token)
   (let $token-text (lib_parse:atom-text $token)
     (PApp (lib_parse:literal-label "token" $token-text) LNil)))

(= (lib_parse:sort-pattern $sort)
   (let $sort-text (lib_parse:atom-text $sort)
     (PApp (lib_parse:literal-label "sort" $sort-text) LNil)))

(= (lib_parse:boundary-label $index)
   (let $index-text (lib_parse:index-text $index)
     (lib_parse:literal-label "boundary" $index-text)))

(= (lib_parse:boundary-pattern $index)
   (PApp (lib_parse:boundary-label $index) LNil))

(= (lib_parse:boundary-name $index)
   (let $index-text (lib_parse:index-text $index)
     (str:concat "boundary" $index-text)))

(= (lib_parse:tree-name $index)
   (let $index-text (lib_parse:index-text $index)
     (str:concat "tree" $index-text)))

(= (lib_parse:boundary-variable $index)
   (FVar (lib_parse:boundary-name $index)))

(= (lib_parse:tree-variable $index)
   (FVar (lib_parse:tree-name $index)))

; ---------- Source-indexed judgment constructors ---------------------------
(= (lib_parse:boundary-judgment $source $boundary)
   (PApp "__lib_parse.Boundary"
     (LCons $source (LCons $boundary LNil))))

(= (lib_parse:token-span-judgment $source $left $right $token)
   (PApp "__lib_parse.TokenSpan"
     (LCons $source
       (LCons $left
         (LCons $right (LCons $token LNil))))))

(= (lib_parse:derives-judgment $source $sort $left $right $tree)
   (PApp "__lib_parse.GrammarDerives"
     (LCons $source
       (LCons $sort
         (LCons $left
           (LCons $right (LCons $tree LNil)))))))

(= (lib_parse:derives-node-judgment $source $sort $left $right)
   (PApp "__lib_parse.GrammarDerivesNode"
     (LCons $source
       (LCons $sort
         (LCons $left (LCons $right LNil))))))

(= (lib_parse:judgments)
   (LCons (JDecl "__lib_parse.Boundary" 2)
     (LCons (JDecl "__lib_parse.TokenSpan" 4)
       (LCons (JDecl "__lib_parse.GrammarDerives" 5) LNil))))

(= (lib_parse:dag-judgments)
   (LCons (JDecl "__lib_parse.Boundary" 2)
     (LCons (JDecl "__lib_parse.TokenSpan" 4)
       (LCons (JDecl "__lib_parse.GrammarDerivesNode" 4) LNil))))

; ---------- Constructor declaration generation ----------------------------
(= (lib_parse:decl-add $head $arity LNil)
   (LCons (CDecl $head $arity) LNil))
(= (lib_parse:decl-add $head $arity
      (LCons (CDecl $existing-head $existing-arity) $rest))
   (if (and (== $head $existing-head) (== $arity $existing-arity))
     (LCons (CDecl $existing-head $existing-arity) $rest)
     (LCons (CDecl $existing-head $existing-arity)
       (lib_parse:decl-add $head $arity $rest))))

(= (lib_parse:literal-decl-add $kind $payload $decls)
   (lib_parse:decl-add (lib_parse:literal-label $kind $payload) 0 $decls))

(= (lib_parse:token-decl-add $token $decls)
   (let $token-text (lib_parse:atom-text $token)
     (lib_parse:literal-decl-add "token" $token-text $decls)))

(= (lib_parse:sort-decl-add $sort $decls)
   (let $sort-text (lib_parse:atom-text $sort)
     (lib_parse:literal-decl-add "sort" $sort-text $decls)))

(= (lib_parse:template-hole-count $template)
   (case $template
     ((Nil 0)
      ((Cons (Tm $token) $rest)
       (lib_parse:template-hole-count $rest))
      ((Cons (Hl $sort) $rest)
       (+ 1 (lib_parse:template-hole-count $rest)))
      ((Cons (HlB $sort $scope) $rest)
       (+ 1 (lib_parse:template-hole-count $rest)))
      ($other (LPInferenceError unsupported-template)))))

(= (lib_parse:template-decls $template $decls)
   (case $template
     ((Nil $decls)
      ((Cons (Tm $token) $rest)
       (lib_parse:template-decls $rest
         (lib_parse:token-decl-add $token $decls)))
      ((Cons (Hl $sort) $rest)
       (lib_parse:template-decls $rest
         (lib_parse:sort-decl-add $sort $decls)))
      ((Cons (HlB $sort $scope) $rest)
       (lib_parse:template-decls $rest
         (lib_parse:sort-decl-add $scope
           (lib_parse:sort-decl-add $sort $decls))))
      ($other (LPInferenceError unsupported-template)))))

(= (lib_parse:grammar-decls $grammar $decls)
   (case $grammar
     ((Nil $decls)
      ((Cons (Prod $label $sort $template) $rest)
       (let $arity (lib_parse:template-hole-count $template)
         (let $label-text (lib_parse:atom-text $label)
           (let $with-constructor
             (lib_parse:decl-add $label-text $arity $decls)
             (let $with-sort
               (lib_parse:sort-decl-add $sort $with-constructor)
               (lib_parse:grammar-decls $rest
                 (lib_parse:template-decls $template $with-sort)))))))
      ((Cons (VarD $token $sort) $rest)
       (lib_parse:grammar-decls $rest
         (lib_parse:token-decl-add $token
           (lib_parse:sort-decl-add $sort $decls))))
      ((Cons (LexD $class $sort) $rest)
       (lib_parse:grammar-decls $rest
         (lib_parse:sort-decl-add $sort $decls)))
      ($other (LPInferenceError unsupported-grammar-entry)))))

(= (lib_parse:source-token-decls $tokens $decls)
   (case $tokens
     ((Nil $decls)
      ((Cons $token $rest)
       (lib_parse:source-token-decls $rest
         (lib_parse:token-decl-add $token $decls)))
      ($other (LPInferenceError malformed-token-ledger)))))

; Each source position is a constant-depth constructor.  The enclosing
; judgments still bind it to the exact source identity.
(= (lib_parse:boundary-decls $tokens $index)
   (case $tokens
     ((Nil
       (LCons (CDecl (lib_parse:boundary-label $index) 0) LNil))
      ((Cons $token $rest)
       (LCons (CDecl (lib_parse:boundary-label $index) 0)
         (lib_parse:boundary-decls $rest (+ $index 1))))
      ($other (LPInferenceError malformed-token-ledger)))))

(= (lib_parse:constructors $grammar $source $tokens)
   (let $base
     (lib_parse:decl-add "__lib_parse.leaf" 1
       (lib_parse:literal-decl-add "source" $source LNil))
     (let $with-source-tokens
       (lib_parse:source-token-decls $tokens $base)
       (let $with-boundaries
         (lib_parse:append $with-source-tokens
           (lib_parse:boundary-decls $tokens 0))
         (lib_parse:grammar-decls $grammar
           $with-boundaries)))))

; ---------- Ground source-ledger rules -------------------------------------
(= (lib_parse:boundary-rule $source $index)
   (let $payload (lib_parse:indexed-payload $source $index)
     (GRuleV1 (lib_parse:rule-id "boundary" $payload)
       LNil LNil
       (lib_parse:boundary-judgment
         (lib_parse:source-pattern $source)
         (lib_parse:boundary-pattern $index))
       LNil)))

(= (lib_parse:token-rule $source $index $token)
   (let $payload (lib_parse:indexed-payload $source $index)
     (GRuleV1 (lib_parse:rule-id "token" $payload)
       LNil LNil
       (lib_parse:token-span-judgment
         (lib_parse:source-pattern $source)
         (lib_parse:boundary-pattern $index)
         (lib_parse:boundary-pattern (+ $index 1))
         (lib_parse:token-pattern $token))
       LNil)))

(= (lib_parse:leaf-tree $token)
   (PApp "__lib_parse.leaf"
     (LCons (lib_parse:token-pattern $token) LNil)))

(= (lib_parse:leaf-rule $source $index $token $sort)
   (let $payload (lib_parse:indexed-payload $source $index)
     (GRuleV1 (lib_parse:rule-id "leaf" $payload)
       LNil LNil
       (lib_parse:derives-judgment
         (lib_parse:source-pattern $source)
         (lib_parse:sort-pattern $sort)
         (lib_parse:boundary-pattern $index)
         (lib_parse:boundary-pattern (+ $index 1))
         (lib_parse:leaf-tree $token))
       LNil)))

(= (lib_parse:leaf-node-rule $source $index $token $sort)
   (let $payload (lib_parse:indexed-payload $source $index)
     (GRuleV1 (lib_parse:rule-id "leaf" $payload)
       LNil LNil
       (lib_parse:derives-node-judgment
         (lib_parse:source-pattern $source)
         (lib_parse:sort-pattern $sort)
         (lib_parse:boundary-pattern $index)
         (lib_parse:boundary-pattern (+ $index 1)))
       LNil)))

(= (lib_parse:boundary-rules-onto $tokens $source $index $tail)
   (case $tokens
     ((Nil (LCons (lib_parse:boundary-rule $source $index) $tail))
      ((Cons $token $rest)
       (LCons (lib_parse:boundary-rule $source $index)
         (lib_parse:boundary-rules-onto
           $rest $source (+ $index 1) $tail)))
      ($other (LPInferenceError malformed-token-ledger)))))

(= (lib_parse:boundary-rules $tokens $source $index)
   (lib_parse:boundary-rules-onto $tokens $source $index LNil))

(= (lib_parse:token-rules-onto $tokens $source $index $tail)
   (case $tokens
     ((Nil $tail)
      ((Cons $token $rest)
       (LCons (lib_parse:token-rule $source $index $token)
         (lib_parse:token-rules-onto
           $rest $source (+ $index 1) $tail)))
      ($other (LPInferenceError malformed-token-ledger)))))

(= (lib_parse:token-rules $tokens $source $index)
   (lib_parse:token-rules-onto $tokens $source $index LNil))

(= (lib_parse:leaf-rules-onto $grammar $tokens $source $index $tail)
   (case $tokens
     ((Nil $tail)
      ((Cons $token $rest)
       (case (var-nt $grammar $token)
         (((Err $reason)
           (lib_parse:leaf-rules-onto
             $grammar $rest $source (+ $index 1) $tail))
          ($sort
           (LCons (lib_parse:leaf-rule $source $index $token $sort)
             (lib_parse:leaf-rules-onto
               $grammar $rest $source (+ $index 1) $tail))))))
      ($other (LPInferenceError malformed-token-ledger)))))

(= (lib_parse:leaf-rules $grammar $tokens $source $index)
   (lib_parse:leaf-rules-onto $grammar $tokens $source $index LNil))

(= (lib_parse:leaf-node-rules-onto
      $grammar $tokens $source $index $tail)
   (case $tokens
     ((Nil $tail)
      ((Cons $token $rest)
       (case (var-nt $grammar $token)
         (((Err $reason)
           (lib_parse:leaf-node-rules-onto
             $grammar $rest $source (+ $index 1) $tail))
          ($sort
           (LCons (lib_parse:leaf-node-rule $source $index $token $sort)
             (lib_parse:leaf-node-rules-onto
               $grammar $rest $source (+ $index 1) $tail))))))
      ($other (LPInferenceError malformed-token-ledger)))))

(= (lib_parse:leaf-node-rules $grammar $tokens $source $index)
   (lib_parse:leaf-node-rules-onto
     $grammar $tokens $source $index LNil))

; ---------- Grammar production schemas ------------------------------------
(= (lib_parse:formal-range $prefix $index $count)
   (case $count
     ((0 LNil)
      ($positive
       (if (> $positive 0)
         (let $name
           (if (== $prefix "boundary")
             (lib_parse:boundary-name $index)
             (lib_parse:tree-name $index))
           (LCons (Formal $name 0)
             (lib_parse:formal-range
               $prefix (+ $index 1) (- $positive 1))))
         LNil)))))

(= (lib_parse:template-size $template)
   (case $template
     ((Nil 0)
      ((Cons $item $rest) (+ 1 (lib_parse:template-size $rest)))
      ($other (LPInferenceError unsupported-template)))))

(= (lib_parse:template-premises $template $boundary-index $tree-index)
   (case $template
     ((Nil LNil)
      ((Cons (Tm $token) $rest)
       (LCons
         (lib_parse:token-span-judgment
           (FVar "source")
           (lib_parse:boundary-variable $boundary-index)
           (lib_parse:boundary-variable (+ $boundary-index 1))
           (lib_parse:token-pattern $token))
         (lib_parse:template-premises
           $rest (+ $boundary-index 1) $tree-index)))
      ((Cons (Hl $sort) $rest)
       (LCons
         (lib_parse:derives-judgment
           (FVar "source")
           (lib_parse:sort-pattern $sort)
           (lib_parse:boundary-variable $boundary-index)
           (lib_parse:boundary-variable (+ $boundary-index 1))
           (lib_parse:tree-variable $tree-index))
         (lib_parse:template-premises
           $rest (+ $boundary-index 1) (+ $tree-index 1))))
      ((Cons (HlB $sort $scope) $rest)
       (LCons
         (lib_parse:derives-judgment
           (FVar "source")
           (lib_parse:sort-pattern $sort)
           (lib_parse:boundary-variable $boundary-index)
           (lib_parse:boundary-variable (+ $boundary-index 1))
           (lib_parse:tree-variable $tree-index))
         (lib_parse:template-premises
           $rest (+ $boundary-index 1) (+ $tree-index 1))))
      ($other (LPInferenceError unsupported-template)))))

(= (lib_parse:template-children $template $tree-index)
   (case $template
     ((Nil LNil)
      ((Cons (Tm $token) $rest)
       (lib_parse:template-children $rest $tree-index))
      ((Cons (Hl $sort) $rest)
       (LCons (lib_parse:tree-variable $tree-index)
         (lib_parse:template-children $rest (+ $tree-index 1))))
      ((Cons (HlB $sort $scope) $rest)
       (LCons (lib_parse:tree-variable $tree-index)
         (lib_parse:template-children $rest (+ $tree-index 1))))
      ($other (LPInferenceError unsupported-template)))))

(= (lib_parse:production-rule $label $sort $template)
   (let $label-text (lib_parse:atom-text $label)
     (let $template-size (lib_parse:template-size $template)
       (let $hole-count (lib_parse:template-hole-count $template)
         (let $boundary-formals
           (lib_parse:formal-range "boundary" 0 (+ $template-size 1))
           (let $tree-formals
             (lib_parse:formal-range "tree" 0 $hole-count)
             (let $formals
               (LCons (Formal "source" 0)
                 (lib_parse:append $boundary-formals $tree-formals))
               (let $premises
                 (case $template
                   ((Nil
                     (LCons
                       (lib_parse:boundary-judgment
                         (FVar "source")
                         (lib_parse:boundary-variable 0))
                       LNil))
                    ($nonempty
                     (lib_parse:template-premises $template 0 0))))
                 (GRuleV1 (lib_parse:rule-id "production" $label-text)
                   $formals
                   $premises
                   (lib_parse:derives-judgment
                     (FVar "source")
                     (lib_parse:sort-pattern $sort)
                     (lib_parse:boundary-variable 0)
                     (lib_parse:boundary-variable $template-size)
                     (PApp $label-text
                       (lib_parse:template-children $template 0)))
                   LNil)))))))))

(= (lib_parse:production-rules $grammar)
   (case $grammar
     ((Nil LNil)
      ((Cons (Prod $label $sort $template) $rest)
       (LCons (lib_parse:production-rule $label $sort $template)
         (lib_parse:production-rules $rest)))
      ((Cons (VarD $token $sort) $rest)
       (lib_parse:production-rules $rest))
      ((Cons (LexD $class $sort) $rest)
       (lib_parse:production-rules $rest))
      ($other (LPInferenceError unsupported-grammar-entry)))))

; Compact production schemas retain the same source, boundary, rule, and
; ordered-premise data while omitting repeated child-tree payloads.
(= (lib_parse:template-node-premises $template $boundary-index)
   (case $template
     ((Nil LNil)
      ((Cons (Tm $token) $rest)
       (LCons
         (lib_parse:token-span-judgment
           (FVar "source")
           (lib_parse:boundary-variable $boundary-index)
           (lib_parse:boundary-variable (+ $boundary-index 1))
           (lib_parse:token-pattern $token))
         (lib_parse:template-node-premises
           $rest (+ $boundary-index 1))))
      ((Cons (Hl $sort) $rest)
       (LCons
         (lib_parse:derives-node-judgment
           (FVar "source")
           (lib_parse:sort-pattern $sort)
           (lib_parse:boundary-variable $boundary-index)
           (lib_parse:boundary-variable (+ $boundary-index 1)))
         (lib_parse:template-node-premises
           $rest (+ $boundary-index 1))))
      ((Cons (HlB $sort $scope) $rest)
       (LCons
         (lib_parse:derives-node-judgment
           (FVar "source")
           (lib_parse:sort-pattern $sort)
           (lib_parse:boundary-variable $boundary-index)
           (lib_parse:boundary-variable (+ $boundary-index 1)))
         (lib_parse:template-node-premises
           $rest (+ $boundary-index 1))))
      ($other (LPInferenceError unsupported-template)))))

(= (lib_parse:production-node-rule $label $sort $template)
   (let $label-text (lib_parse:atom-text $label)
     (let $template-size (lib_parse:template-size $template)
       (let $boundary-formals
         (lib_parse:formal-range "boundary" 0 (+ $template-size 1))
         (let $formals
           (LCons (Formal "source" 0) $boundary-formals)
           (let $premises
             (case $template
               ((Nil
                 (LCons
                   (lib_parse:boundary-judgment
                     (FVar "source")
                     (lib_parse:boundary-variable 0))
                   LNil))
                ($nonempty
                 (lib_parse:template-node-premises $template 0))))
             (GRuleV1 (lib_parse:rule-id "production" $label-text)
               $formals
               $premises
               (lib_parse:derives-node-judgment
                 (FVar "source")
                 (lib_parse:sort-pattern $sort)
                 (lib_parse:boundary-variable 0)
                 (lib_parse:boundary-variable $template-size))
               LNil)))))))

(= (lib_parse:production-node-rules $grammar)
   (case $grammar
     ((Nil LNil)
      ((Cons (Prod $label $sort $template) $rest)
       (LCons (lib_parse:production-node-rule $label $sort $template)
         (lib_parse:production-node-rules $rest)))
      ((Cons (VarD $token $sort) $rest)
       (lib_parse:production-node-rules $rest))
      ((Cons (LexD $class $sort) $rest)
       (lib_parse:production-node-rules $rest))
      ($other (LPInferenceError unsupported-grammar-entry)))))

; ---------- Language generation and admission --------------------------
(= (lib_parse:source-valid $source $tokens)
   (case $tokens
     ((Nil (if (== $source "") False True))
      ((Cons $token $rest)
       (if (== $source "") False
         (if (== $token "") False
           (lib_parse:source-valid $source $rest))))
      ($other False))))

(= (lib_parse:raw-language $grammar $source $tokens)
   (GInferenceLanguageV1 1
     (lib_parse:constructors $grammar $source $tokens)
     (lib_parse:judgments)
     (lib_parse:boundary-rules-onto $tokens $source 0
       (lib_parse:token-rules-onto $tokens $source 0
         (lib_parse:leaf-rules-onto $grammar $tokens $source 0
           (lib_parse:production-rules $grammar))))
     GNoConversion))

(= (lib_parse:raw-dag-language $grammar $source $tokens)
   (GInferenceLanguageV1 1
     (lib_parse:constructors $grammar $source $tokens)
     (lib_parse:dag-judgments)
     (lib_parse:boundary-rules-onto $tokens $source 0
       (lib_parse:token-rules-onto $tokens $source 0
         (lib_parse:leaf-node-rules-onto $grammar $tokens $source 0
           (lib_parse:production-node-rules $grammar))))
     GNoConversion))

(= (lib_parse:raw-language-optimized $grammar $source $tokens)
   (function
     (case (gparse:inference-language $grammar $source $tokens)
       (((GInferenceLanguageV1
            $version $constructors $judgments $rules $conversion)
         (return (GInferenceLanguageV1
           $version $constructors $judgments $rules $conversion)))
        ((Error $where $reason)
         (return
           (LPInferenceError
             (native-language-rejected $where $reason))))
        ($other
         (case (lib_parse:source-valid $source $tokens)
           ((True
             (case (lib_parse:raw-language $grammar $source $tokens)
               (($language (return $language)))))
            ($invalid
             (return (LPInferenceError invalid-source-ledger))))))))))

(: lib_parse:indexed-language-fields-valid
   (-> Atom Atom Atom Atom Atom Bool))

; `generate-language` has already exposed the fields of the canonical flat
; language.  Compile those fields directly instead of reconstructing the
; deeply nested artifact merely to destructure it again.  This is the
; specialized lowering of the generic `gic-build-index` boundary; both use
; `gic-build-index-fields-in`, so the admission judgment is unchanged.
(= (lib_parse:indexed-language-fields-valid
      $version $constructors $judgments $rules $conversion)
   (let $space (new-space)
     (case
       (gic-build-index-fields-in
         $space $version $constructors $judgments $rules $conversion)
     (((GICIndexOK $space) True)
      (GICIndexFail False)
      ((Error $where $reason)
       (let $fallback-space (new-space pathmap)
         (case
           (gic-build-index-fields-in
             $fallback-space $version $constructors $judgments
             $rules $conversion)
           (((GICIndexOK $indexed-space) True)
            ($fallback-other False)))))
      ($other False)))))

(= (lib_parse:language-candidate-admitted $grammar $source $tokens)
   (function
     (case (lp-admit $grammar)
       ((Admitted
         (case (lib_parse:raw-language-optimized
                 $grammar $source $tokens)
           (((GInferenceLanguageV1
                $version $constructors $judgments $rules $conversion)
             (return
               (LPInferenceLanguage
                 (GInferenceLanguageV1
                   $version $constructors $judgments $rules $conversion))))
            ((LPInferenceError $reason)
             (return (LPInferenceError $reason)))
            ($other
             (return (LPInferenceError invalid-generated-language))))))
        ($rejected
         (return (LPInferenceError grammar-not-admitted)))))))

(= (lib_parse:language-candidate $grammar $source $tokens)
   (function
     (case (lib_parse:language-candidate-admitted
             $grammar $source $tokens)
       (($result (return $result))))))

; DAG language generation uses the same admitted grammar and source
; ledger, but derives the shared GrammarDerivesNode judgment.  There is no
; hand-authored fallback: failure of the grammar-derived producer rejects.
(= (lib_parse:dag-language-candidate $grammar $source $tokens)
   (function
     (case (lp-admit $grammar)
       ((Admitted
         (case (gparse:inference-dag-language
                 $grammar $source $tokens)
           (((GInferenceLanguageV1
                $version $constructors $judgments $rules $conversion)
             (return
               (LPInferenceLanguage
                 (GInferenceLanguageV1
                   $version $constructors $judgments $rules $conversion))))
            ((Error $where $reason)
             (return
               (LPInferenceError
                 (native-dag-language-rejected $where $reason))))
            ($other
             (return (LPInferenceError invalid-dag-language))))))
        ($rejected
         (return (LPInferenceError grammar-not-admitted)))))))

(= (lib_parse:generate-language $grammar $source $tokens)
   (function
     (case (lib_parse:language-candidate $grammar $source $tokens)
       (((LPInferenceLanguage
            (GInferenceLanguageV1
              $version $constructors $judgments $rules $conversion))
         (if (lib_parse:indexed-language-fields-valid
               $version $constructors $judgments $rules $conversion)
           (return
             (LPInferenceLanguage
               (GInferenceLanguageV1
                 $version $constructors $judgments $rules $conversion)))
           (return (LPInferenceError invalid-generated-language))))
        ($error (return $error))))))

; ---------- Shared-tree to GProof lowering ---------------------------------
(= (lib_parse:boundary-proof $source $index)
   (let $payload (lib_parse:indexed-payload $source $index)
     (GProof
       (GRuleInst (lib_parse:rule-id "boundary" $payload) LNil)
       PrNil)))

(= (lib_parse:token-proof $source $index)
   (let $payload (lib_parse:indexed-payload $source $index)
     (GProof
       (GRuleInst (lib_parse:rule-id "token" $payload) LNil)
       PrNil)))

(= (lib_parse:leaf-proof $source $index)
   (let $payload (lib_parse:indexed-payload $source $index)
     (GProof
       (GRuleInst (lib_parse:rule-id "leaf" $payload) LNil)
       PrNil)))

(= (lib_parse:lower-empty-kids $source $left $right $kids)
   (case $kids
     (((Cons (EpsC) Nil)
       (if (== $left $right)
         (LPKidsProof
           $right LNil LNil
           (PrCons (lib_parse:boundary-proof $source $left) PrNil))
         (LPInferenceError bad-empty-span)))
      ($other (LPInferenceError bad-empty-witness)))))

(= (lib_parse:lower-kids $grammar $source $template $kids $position)
   (case $template
     ((Nil
       (case $kids
         ((Nil (LPKidsProof $position LNil LNil PrNil))
          ($other (LPInferenceError extra-parser-child)))))
      ((Cons (Tm $expected) $rest-template)
       (case $kids
         (((Cons (TokC $actual $index) $rest-kids)
           (if (and (== $expected $actual) (== $index $position))
             (case (lib_parse:lower-kids
                     $grammar $source $rest-template $rest-kids
                     (+ $position 1))
               (((LPKidsProof $end $boundaries $trees $proofs)
                 (LPKidsProof $end
                   (LCons
                     (lib_parse:boundary-pattern (+ $position 1))
                     $boundaries)
                   $trees
                   (PrCons
                     (lib_parse:token-proof $source $position)
                     $proofs)))
                ($error $error)))
             (LPInferenceError terminal-child-mismatch)))
          ($other (LPInferenceError terminal-child-shape)))))
      ((Cons (Hl $sort) $rest-template)
       (lib_parse:lower-hole
         $grammar $source $sort $rest-template $kids $position))
      ((Cons (HlB $sort $scope) $rest-template)
       (lib_parse:lower-hole
         $grammar $source $sort $rest-template $kids $position))
      ($other (LPInferenceError unsupported-parser-child)))))

(= (lib_parse:lower-hole $grammar $source $expected-sort
      $rest-template $kids $position)
   (case $kids
     (((Cons $child $rest-kids)
       (case (lib_parse:lower-tree $grammar $source $child)
         (((LPTreeProof $left $right $actual-sort $tree $proof)
           (if (and (== $left $position) (== $actual-sort $expected-sort))
             (case (lib_parse:lower-kids
                     $grammar $source $rest-template $rest-kids $right)
               (((LPKidsProof $end $boundaries $trees $proofs)
                 (LPKidsProof $end
                   (LCons (lib_parse:boundary-pattern $right) $boundaries)
                   (LCons $tree $trees)
                   (PrCons $proof $proofs)))
                ($error $error)))
             (LPInferenceError nonterminal-child-mismatch)))
          ($error $error))))
      ($other (LPInferenceError missing-nonterminal-child)))))

(= (lib_parse:lower-tree $grammar $source $tree)
   (case $tree
     (((LeafC $token $left $right)
       (if (== $right (+ $left 1))
         (case (var-nt $grammar $token)
           (((Err $reason) (LPInferenceError undeclared-leaf))
            ($sort
             (LPTreeProof $left $right $sort
               (lib_parse:leaf-tree $token)
               (lib_parse:leaf-proof $source $left)))))
         (LPInferenceError bad-leaf-span)))
      ((NodeC $label $claimed-sort $left $right $kids)
       (case (prod-nt $grammar $label)
         (((Err $reason) (LPInferenceError unknown-production))
          ($actual-sort
           (if (== $actual-sort $claimed-sort)
             (case (template-of $grammar $label)
               (((Err $reason)
                 (LPInferenceError missing-production-template))
                ($template
                 (lib_parse:lower-production-tree
                   $grammar $source $label $actual-sort
                   $left $right $kids $template))))
             (LPInferenceError claimed-sort-mismatch))))))
      ($other (LPInferenceError unsupported-parser-tree)))))

(= (lib_parse:node-tree-proof $source $label $sort $left $right
      $boundaries $trees $proofs)
   (let $label-text (lib_parse:atom-text $label)
     (let $arguments
       (LCons (lib_parse:source-pattern $source)
         (lib_parse:append $boundaries $trees))
       (LPTreeProof $left $right $sort
         (PApp $label-text $trees)
         (GProof
           (GRuleInst
             (lib_parse:rule-id "production" $label-text)
             $arguments)
           $proofs)))))

(= (lib_parse:lower-production-tree $grammar $source $label $sort
      $left $right $kids $template)
   (case $template
     ((Nil
       (case (lib_parse:lower-empty-kids $source $left $right $kids)
         (((LPKidsProof $end $tail-boundaries $trees $proofs)
           (lib_parse:node-tree-proof $source $label $sort $left $right
             (LCons (lib_parse:boundary-pattern $left) LNil)
             LNil $proofs))
          ($error $error))))
      ((Cons $item $rest)
       (case (lib_parse:lower-kids
               $grammar $source $template $kids $left)
         (((LPKidsProof $end $tail-boundaries $trees $proofs)
           (if (== $end $right)
             (lib_parse:node-tree-proof
               $source $label $sort $left $right
               (LCons
                 (lib_parse:boundary-pattern $left)
                 $tail-boundaries)
               $trees $proofs)
             (LPInferenceError node-span-mismatch)))
          ($error $error))))
      ($other (LPInferenceError unsupported-template)))))

(= (lib_parse:proof-from-shared $grammar $source $start $tokens $cert)
   (case (lib_parse:lower-tree $grammar $source $cert)
     (((LPTreeProof $left $right $sort $tree $proof)
       (if (and (== $left 0)
                (and (== $right (lp-len $tokens)) (== $sort $start)))
         (LPInferenceProof
           (lib_parse:derives-judgment
             (lib_parse:source-pattern $source)
             (lib_parse:sort-pattern $start)
             (lib_parse:boundary-pattern 0)
             (lib_parse:boundary-pattern (lp-len $tokens))
             $tree)
           $proof)
         (LPInferenceError root-index-mismatch)))
      ($error $error))))

(= (lib_parse:check-shared $grammar $source $start $tokens $cert)
   (case (lib_parse:language-candidate $grammar $source $tokens)
     (((LPInferenceLanguage $language)
       (case (lib_parse:proof-from-shared
               $grammar $source $start $tokens $cert)
         (((LPInferenceProof $goal $proof)
           (gic-check $language $goal $proof))
          ($error False))))
      ($error False))))

(= (lib_parse:slr-check $path $definition $grammar
      $source $start $tokens)
   (case (gparse:slr-parse-shared $path $definition $start $tokens)
     (((Unique $cert)
       (lib_parse:check-shared $grammar $source $start $tokens $cert))
      (Ambiguous False)
      (NoParse False)
      ($error False))))
