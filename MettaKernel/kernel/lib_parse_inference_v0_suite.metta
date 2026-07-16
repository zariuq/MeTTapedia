!(import! &self lib_parse_inference_v0)

(= (lpi:presentation-class $result)
   (case $result
     (((LPInferencePresentation $presentation) Presentation)
      ((LPInferenceError $reason) Error)
      ($other Other))))

(= (lpi:proof-class $result)
   (case $result
     (((LPInferenceProof $goal $proof) Proof)
      ((LPInferenceError $reason) Error)
      ($other Other))))

(= (lpi:terminal-grammar)
   (Cons (Prod lit Expr (Cons (Tm a) Nil)) Nil))

(= (lpi:terminal-tokens) (Cons a Nil))
(= (lpi:terminal-tokens-flat) (a))

(= (lpi:terminal-cert)
   (NodeC lit Expr 0 1 (Cons (TokC a 0) Nil)))

(= (lpi:terminal-native-dag)
   (gparse:inference-dag-proof
     (lpi:terminal-grammar) "terminal-source" Expr
     (lpi:terminal-tokens) (lpi:terminal-cert)))

(= (lpi:recursive-grammar)
   (Cons (Prod zero Expr (Cons (Tm zero) Nil))
     (Cons
       (Prod paren Expr
         (Cons (Tm lparen)
           (Cons (Hl Expr) (Cons (Tm rparen) Nil))))
       Nil)))

(= (lpi:recursive-tokens)
   (Cons lparen (Cons zero (Cons rparen Nil))))

(= (lpi:recursive-cert)
   (NodeC paren Expr 0 3
     (Cons (TokC lparen 0)
       (Cons
         (NodeC zero Expr 1 2 (Cons (TokC zero 1) Nil))
         (Cons (TokC rparen 2) Nil)))))

(= (lpi:variable-grammar) (Cons (VarD x Expr) Nil))
(= (lpi:variable-tokens) (Cons x Nil))
(= (lpi:variable-cert) (LeafC x 0 1))

(= (lpi:lexical-grammar) (Cons (LexD Ident Expr) Nil))
(= (lpi:lexical-token) (Lex Ident "name"))
(= (lpi:lexical-tokens) (Cons (lpi:lexical-token) Nil))
(= (lpi:lexical-cert) (LeafC (lpi:lexical-token) 0 1))

(= (lpi:empty-grammar) (Cons (Prod empty Expr Nil) Nil))
(= (lpi:empty-cert) (NodeC empty Expr 0 0 (Cons (EpsC) Nil)))

(= (lpi:mixed-binder-grammar)
   (Cons (LexD Ident Expr)
     (Cons (Prod bind Expr (Cons (HlB Expr Scope) Nil))
       (Cons (VarD x Expr) Nil))))

(= (lpi:validity-pair $presentation)
   (ValidityPair
     (gic-presentation-valid $presentation)
     (lib_parse:indexed-presentation-valid $presentation)))

(= (lpi:duplicate-first-rule $presentation)
   (case $presentation
     (((GPresentation $constructors $judgments
          (LCons $rule $rest))
       (GPresentation $constructors $judgments
         (LCons $rule (LCons $rule $rest))))
      ($other $other))))

(= (lpi:drop-first-constructor $presentation)
   (case $presentation
     (((GPresentation (LCons $first $rest) $judgments $rules)
       (GPresentation $rest $judgments $rules))
      ($other $other))))

(= (lpi:change-first-constructor-arity $presentation)
   (case $presentation
     (((GPresentation
          (LCons (CDecl $head $arity) $rest) $judgments $rules)
       (GPresentation
         (LCons (CDecl $head (+ $arity 1)) $rest) $judgments $rules))
      ($other $other))))

(= (lpi:check-dag-blocks $presentation $goal $root $blocks)
   (case (gic-build-index $presentation)
     (((GICIndexOK $space)
       (gic-index-check-dag-blocks-valid $space $goal $root $blocks))
      ($_ False))))

(= (lpi:check-native-dag $grammar $source $tokens $result)
   (case $result
     (((LPInferenceDagBlocks $goal $root $blocks $count)
       (lpi:check-dag-blocks
         (lib_parse:raw-dag-presentation $grammar $source $tokens)
         $goal $root $blocks))
      ($other False))))

(= (lpi:check-native-dag-wrong-root $grammar $source $tokens $result)
   (case $result
     (((LPInferenceDagBlocks $goal $root $blocks $count)
       (lpi:check-dag-blocks
         (lib_parse:raw-dag-presentation $grammar $source $tokens)
         $goal 0 $blocks))
      ($other False))))

(= (lpi:check-native-dag-reversed $grammar $source $tokens $result)
   (case $result
     (((LPInferenceDagBlocks $goal $root
          (LCons (LCons $first (LCons $second LNil)) LNil) $count)
       (lpi:check-dag-blocks
         (lib_parse:raw-dag-presentation $grammar $source $tokens)
         $goal $root
         (LCons (LCons $second (LCons $first LNil)) LNil)))
      ($other False))))

(= (lpi:check-native-dag-missing-child $grammar $source $tokens $result)
   (case $result
     (((LPInferenceDagBlocks $goal $root
          (LCons
            (LCons $first
              (LCons (GDNode $id $instance (DrCons $child DrNil)) LNil))
            LNil)
          $count)
       (lpi:check-dag-blocks
         (lib_parse:raw-dag-presentation $grammar $source $tokens)
         $goal $root
         (LCons
           (LCons $first
             (LCons (GDNode $id $instance (DrCons 99 DrNil)) LNil))
           LNil)))
      ($other False))))

(= (lpi:check-native-dag-duplicate-id $grammar $source $tokens $result)
   (case $result
     (((LPInferenceDagBlocks $goal $root
          (LCons
            (LCons (GDNode $first-id $first-instance $first-children)
              (LCons (GDNode $second-id $second-instance $second-children)
                LNil))
            LNil)
          $count)
       (lpi:check-dag-blocks
         (lib_parse:raw-dag-presentation $grammar $source $tokens)
         $goal $root
         (LCons
           (LCons (GDNode $first-id $first-instance $first-children)
             (LCons
               (GDNode $first-id $second-instance $second-children) LNil))
           LNil)))
      ($other False))))

(= (lpi:check-native-dag-reversed-blocks $grammar $source $tokens $result)
   (case $result
     (((LPInferenceDagBlocks $goal $root
          (LCons (LCons $first (LCons $second LNil)) LNil) $count)
       (lpi:check-dag-blocks
         (lib_parse:raw-dag-presentation $grammar $source $tokens)
         $goal $root
         (LCons (LCons $second LNil)
           (LCons (LCons $first LNil) LNil))))
      ($other False))))

; Deterministic helpers must each yield exactly one result.
!(assertEqual
  (collapse
    (lib_parse:source-valid "terminal-source" (lpi:terminal-tokens)))
  (True))

!(assertEqual
  (collapse (lib_parse:source-valid "terminal-source" malformed))
  (False))

!(assertEqual
  (collapse
    (lpi:presentation-class
      (lib_parse:generate-presentation
        (lpi:terminal-grammar) "terminal-source" (lpi:terminal-tokens))))
  (Presentation))

!(assertEqual
  (collapse
    (lpi:proof-class
      (lib_parse:proof-from-shared
        (lpi:terminal-grammar) "terminal-source" Expr
        (lpi:terminal-tokens) (lpi:terminal-cert))))
  (Proof))

; Indexed admission must agree with the reference predicate on the positive
; fixture and on distinct signature/rule mutations.
!(assertEqual
  (collapse
    (lpi:validity-pair
      (lib_parse:raw-presentation
        (lpi:terminal-grammar) "terminal-source" (lpi:terminal-tokens))))
  ((ValidityPair True True)))

!(assertEqual
  (collapse
    (lpi:validity-pair
      (lpi:duplicate-first-rule
        (lib_parse:raw-presentation
          (lpi:terminal-grammar) "terminal-source" (lpi:terminal-tokens)))))
  ((ValidityPair False False)))

; The native producer is an optimization of the executable reference, not a
; second presentation semantics.  Pin exact equality across every v0 form.
!(assertEqual
  (collapse
    (==
      (gparse:inference-presentation
        (lpi:terminal-grammar) "terminal-source" (lpi:terminal-tokens))
      (lib_parse:raw-presentation
        (lpi:terminal-grammar) "terminal-source" (lpi:terminal-tokens))))
  (True))

; Flat expression ledgers are the stack-safe public transport.  They denote
; the same source sequence as the older Cons/Nil representation.
!(assertEqual
  (collapse
    (==
      (gparse:inference-presentation
        (lpi:terminal-grammar) "terminal-source"
        (lpi:terminal-tokens-flat))
      (lib_parse:raw-presentation
        (lpi:terminal-grammar) "terminal-source" (lpi:terminal-tokens))))
  (True))

!(assertEqual
  (collapse
    (lpi:presentation-class
      (lib_parse:presentation-candidate
        (lpi:terminal-grammar) "terminal-source"
        (lpi:terminal-tokens-flat))))
  (Presentation))

!(assertEqual
  (collapse
    (lpi:presentation-class
      (lib_parse:presentation-candidate
        (lpi:terminal-grammar) "" (lpi:terminal-tokens-flat))))
  (Error))

!(assertEqual
  (collapse
    (==
      (gparse:inference-presentation
        (lpi:recursive-grammar) "recursive-source" (lpi:recursive-tokens))
      (lib_parse:raw-presentation
        (lpi:recursive-grammar) "recursive-source" (lpi:recursive-tokens))))
  (True))

!(assertEqual
  (collapse
    (==
      (gparse:inference-presentation
        (lpi:variable-grammar) "variable-source" (lpi:variable-tokens))
      (lib_parse:raw-presentation
        (lpi:variable-grammar) "variable-source" (lpi:variable-tokens))))
  (True))

!(assertEqual
  (collapse
    (==
      (gparse:inference-presentation
        (lpi:lexical-grammar) "lexical-source" (lpi:lexical-tokens))
      (lib_parse:raw-presentation
        (lpi:lexical-grammar) "lexical-source" (lpi:lexical-tokens))))
  (True))

!(assertEqual
  (collapse
    (==
      (gparse:inference-presentation
        (lpi:empty-grammar) "empty-source" Nil)
      (lib_parse:raw-presentation
        (lpi:empty-grammar) "empty-source" Nil)))
  (True))

!(assertEqual
  (collapse
    (==
      (gparse:inference-presentation
        (lpi:mixed-binder-grammar) "mixed-source"
        (Cons (lpi:lexical-token) (Cons x Nil)))
      (lib_parse:raw-presentation
        (lpi:mixed-binder-grammar) "mixed-source"
        (Cons (lpi:lexical-token) (Cons x Nil)))))
  (True))

; The compact native presentation is exactly the independent MeTTa reference
; across terminals, recursion, VarD, LexD, empty productions, and binders.
!(assertEqual
  (collapse
    (==
      (gparse:inference-dag-presentation
        (lpi:terminal-grammar) "terminal-source" (lpi:terminal-tokens))
      (lib_parse:raw-dag-presentation
        (lpi:terminal-grammar) "terminal-source" (lpi:terminal-tokens))))
  (True))

!(assertEqual
  (collapse
    (==
      (gparse:inference-dag-presentation
        (lpi:recursive-grammar) "recursive-source" (lpi:recursive-tokens))
      (lib_parse:raw-dag-presentation
        (lpi:recursive-grammar) "recursive-source" (lpi:recursive-tokens))))
  (True))

!(assertEqual
  (collapse
    (==
      (gparse:inference-dag-presentation
        (lpi:variable-grammar) "variable-source" (lpi:variable-tokens))
      (lib_parse:raw-dag-presentation
        (lpi:variable-grammar) "variable-source" (lpi:variable-tokens))))
  (True))

!(assertEqual
  (collapse
    (==
      (gparse:inference-dag-presentation
        (lpi:lexical-grammar) "lexical-source" (lpi:lexical-tokens))
      (lib_parse:raw-dag-presentation
        (lpi:lexical-grammar) "lexical-source" (lpi:lexical-tokens))))
  (True))

!(assertEqual
  (collapse
    (==
      (gparse:inference-dag-presentation
        (lpi:empty-grammar) "empty-source" Nil)
      (lib_parse:raw-dag-presentation
        (lpi:empty-grammar) "empty-source" Nil)))
  (True))

!(assertEqual
  (collapse
    (==
      (gparse:inference-dag-presentation
        (lpi:mixed-binder-grammar) "mixed-source"
        (Cons (lpi:lexical-token) (Cons x Nil)))
      (lib_parse:raw-dag-presentation
        (lpi:mixed-binder-grammar) "mixed-source"
        (Cons (lpi:lexical-token) (Cons x Nil)))))
  (True))

!(assertEqual
  (collapse
    (lpi:validity-pair
      (lib_parse:raw-dag-presentation
        (lpi:terminal-grammar) "terminal-source" (lpi:terminal-tokens))))
  ((ValidityPair True True)))

; The actual compact proof accepts, while root substitution, node reordering,
; child substitution, duplicate identifiers, and block reordering all reject.
!(assertEqual
  (collapse
    (lpi:check-native-dag
      (lpi:terminal-grammar) "terminal-source" (lpi:terminal-tokens)
      (lpi:terminal-native-dag)))
  (True))

!(assertEqual
  (collapse
    (lpi:check-native-dag-wrong-root
      (lpi:terminal-grammar) "terminal-source" (lpi:terminal-tokens)
      (lpi:terminal-native-dag)))
  (False))

!(assertEqual
  (collapse
    (lpi:check-native-dag-reversed
      (lpi:terminal-grammar) "terminal-source" (lpi:terminal-tokens)
      (lpi:terminal-native-dag)))
  (False))

!(assertEqual
  (collapse
    (lpi:check-native-dag-missing-child
      (lpi:terminal-grammar) "terminal-source" (lpi:terminal-tokens)
      (lpi:terminal-native-dag)))
  (False))

!(assertEqual
  (collapse
    (lpi:check-native-dag-duplicate-id
      (lpi:terminal-grammar) "terminal-source" (lpi:terminal-tokens)
      (lpi:terminal-native-dag)))
  (False))

!(assertEqual
  (collapse
    (lpi:check-native-dag-reversed-blocks
      (lpi:terminal-grammar) "terminal-source" (lpi:terminal-tokens)
      (lpi:terminal-native-dag)))
  (False))

!(assertEqual
  (collapse
    (lpi:validity-pair
      (lpi:drop-first-constructor
        (lib_parse:raw-presentation
          (lpi:terminal-grammar) "terminal-source" (lpi:terminal-tokens)))))
  ((ValidityPair False False)))

!(assertEqual
  (collapse
    (lpi:validity-pair
      (lpi:change-first-constructor-arity
        (lib_parse:raw-presentation
          (lpi:terminal-grammar) "terminal-source" (lpi:terminal-tokens)))))
  ((ValidityPair False False)))

; Positive terminal, recursive, variable, lexical, and empty-production lanes.
!(assertEqual
  (collapse
    (lib_parse:check-shared
      (lpi:terminal-grammar) "terminal-source" Expr
      (lpi:terminal-tokens) (lpi:terminal-cert)))
  (True))

!(assertEqual
  (collapse
    (lib_parse:check-shared
      (lpi:recursive-grammar) "recursive-source" Expr
      (lpi:recursive-tokens) (lpi:recursive-cert)))
  (True))

!(assertEqual
  (collapse
    (lib_parse:check-shared
      (lpi:variable-grammar) "variable-source" Expr
      (lpi:variable-tokens) (lpi:variable-cert)))
  (True))

!(assertEqual
  (collapse
    (lib_parse:check-shared
      (lpi:lexical-grammar) "lexical-source" Expr
      (lpi:lexical-tokens) (lpi:lexical-cert)))
  (True))

!(assertEqual
  (collapse
    (lib_parse:check-shared
      (lpi:empty-grammar) "empty-source" Expr Nil (lpi:empty-cert)))
  (True))

; Mutated token, missing child, claimed sort, and malformed ledger fail closed.
!(assertEqual
  (collapse
    (lib_parse:check-shared
      (lpi:terminal-grammar) "terminal-source" Expr
      (lpi:terminal-tokens)
      (NodeC lit Expr 0 1 (Cons (TokC b 0) Nil))))
  (False))

!(assertEqual
  (collapse
    (lib_parse:check-shared
      (lpi:terminal-grammar) "terminal-source" Expr
      (lpi:terminal-tokens) (NodeC lit Expr 0 1 Nil)))
  (False))

!(assertEqual
  (collapse
    (lib_parse:check-shared
      (lpi:terminal-grammar) "terminal-source" Expr
      (lpi:terminal-tokens)
      (NodeC lit OtherSort 0 1 (Cons (TokC a 0) Nil))))
  (False))

!(assertEqual
  (collapse
    (lpi:presentation-class
      (lib_parse:generate-presentation
        (lpi:terminal-grammar) "terminal-source" malformed)))
  (Error))

!(LPInferenceV0Summary 39 39 0)
