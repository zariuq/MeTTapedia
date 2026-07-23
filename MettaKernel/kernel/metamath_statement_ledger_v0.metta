; Canonical ordered Metamath statement ledger derived from a checked gparse
; source tree.  Parser output is accepted only after the grammar-derived
; inference presentation checks its complete source-indexed derivation.

!(import! &self lib_parse_metamath)
!(import! &self lib_parse_inference_v0)
!(import! &self gslt_checked_source_v1)

(= (metamath-ledger:append Nil $right) $right)
(= (metamath-ledger:append (Cons $head $tail) $right)
   (Cons $head (metamath-ledger:append $tail $right)))

(= (metamath-ledger:span $left $right)
   (MMSourceSpan $left $right))

(= (metamath-ledger:lexical-value
      (LeafC (Lex mm-symbol $value) $left $right))
   $value)
(= (metamath-ledger:label-value
      (LeafC (Lex mm-label $value) $left $right))
   $value)
(= (metamath-ledger:proof-label-value
      (LeafC (Lex mm-proof-label $value) $left $right))
   $value)
(= (metamath-ledger:compressed-value
      (LeafC (Lex mm-compressed-word $value) $left $right))
   $value)
(= (metamath-ledger:include-value
      (LeafC (Lex mm-include-path $value) $left $right))
   $value)

(= (metamath-ledger:symbols
      (NodeC symbols_one symbol_list $left $right
        (Cons $symbol Nil)))
   (Cons (metamath-ledger:lexical-value $symbol) Nil))
(= (metamath-ledger:symbols
      (NodeC symbols_more symbol_list $left $right
        (Cons $symbol (Cons $rest Nil))))
   (Cons (metamath-ledger:lexical-value $symbol)
     (metamath-ledger:symbols $rest)))

(= (metamath-ledger:disjoint-symbols
      (NodeC disjoint_symbols_two disjoint_symbol_list $left $right
        (Cons $first (Cons $second Nil))))
   (Cons (metamath-ledger:lexical-value $first)
     (Cons (metamath-ledger:lexical-value $second) Nil)))
(= (metamath-ledger:disjoint-symbols
      (NodeC disjoint_symbols_more disjoint_symbol_list $left $right
        (Cons $first (Cons $rest Nil))))
   (Cons (metamath-ledger:lexical-value $first)
     (metamath-ledger:disjoint-symbols $rest)))

(= (metamath-ledger:proof-labels
      (NodeC proof_one proof_list $left $right
        (Cons $label Nil)))
   (Cons (metamath-ledger:proof-label-value $label) Nil))
(= (metamath-ledger:proof-labels
      (NodeC proof_more proof_list $left $right
        (Cons $label (Cons $rest Nil))))
   (Cons (metamath-ledger:proof-label-value $label)
     (metamath-ledger:proof-labels $rest)))
(= (metamath-ledger:proof-labels
      (NodeC proof_unknown_one proof_list $left $right
        (Cons (TokC MM_UNKNOWN $unknown) Nil)))
   (Cons "?" Nil))
(= (metamath-ledger:proof-labels
      (NodeC proof_unknown_more proof_list $left $right
        (Cons (TokC MM_UNKNOWN $unknown) (Cons $rest Nil))))
   (Cons "?" (metamath-ledger:proof-labels $rest)))

(= (metamath-ledger:proof-header
      (NodeC header_empty proof_header_list $left $right
        (Cons (EpsC) Nil)))
   Nil)
(= (metamath-ledger:proof-header
      (NodeC header_more proof_header_list $left $right
        (Cons $label (Cons $rest Nil))))
   (Cons (metamath-ledger:proof-label-value $label)
     (metamath-ledger:proof-header $rest)))

(= (metamath-ledger:compressed-words
      (NodeC compressed_one compressed_word_list $left $right
        (Cons $word Nil)))
   (Cons (metamath-ledger:compressed-value $word) Nil))
(= (metamath-ledger:compressed-words
      (NodeC compressed_more compressed_word_list $left $right
        (Cons $word (Cons $rest Nil))))
   (Cons (metamath-ledger:compressed-value $word)
     (metamath-ledger:compressed-words $rest)))

(= (metamath-ledger:statement
      (NodeC statement_const outer_statement $left $right
        (Cons (TokC MM_C $left)
          (Cons $symbols (Cons (TokC MM_DOT $dot) Nil)))))
   (MMStatementConst
     (metamath-ledger:span $left $right)
     (metamath-ledger:symbols $symbols)))

(= (metamath-ledger:statement
      (NodeC statement_var statement $left $right
        (Cons (TokC MM_V $left)
          (Cons $symbols (Cons (TokC MM_DOT $dot) Nil)))))
   (MMStatementVar
     (metamath-ledger:span $left $right)
     (metamath-ledger:symbols $symbols)))

(= (metamath-ledger:statement
      (NodeC statement_disjoint statement $left $right
        (Cons (TokC MM_D $left)
          (Cons $symbols (Cons (TokC MM_DOT $dot) Nil)))))
   (MMStatementDisjoint
     (metamath-ledger:span $left $right)
     (metamath-ledger:disjoint-symbols $symbols)))

(= (metamath-ledger:statement
      (NodeC statement_float statement $left $right
        (Cons $label
          (Cons (TokC MM_F $command)
            (Cons $typecode
              (Cons $variable (Cons (TokC MM_DOT $dot) Nil)))))))
   (MMStatementFloat
     (metamath-ledger:span $left $right)
     (metamath-ledger:label-value $label)
     (metamath-ledger:lexical-value $typecode)
     (metamath-ledger:lexical-value $variable)))

(= (metamath-ledger:statement
      (NodeC statement_essential statement $left $right
        (Cons $label
          (Cons (TokC MM_E $command)
            (Cons $formula (Cons (TokC MM_DOT $dot) Nil))))))
   (MMStatementEssential
     (metamath-ledger:span $left $right)
     (metamath-ledger:label-value $label)
     (metamath-ledger:symbols $formula)))

(= (metamath-ledger:statement
      (NodeC statement_axiom statement $left $right
        (Cons $label
          (Cons (TokC MM_A $command)
            (Cons $formula (Cons (TokC MM_DOT $dot) Nil))))))
   (MMStatementAxiom
     (metamath-ledger:span $left $right)
     (metamath-ledger:label-value $label)
     (metamath-ledger:symbols $formula)))

(= (metamath-ledger:statement
      (NodeC statement_theorem_normal statement $left $right
        (Cons $label
          (Cons (TokC MM_P $command)
            (Cons $formula
              (Cons (TokC MM_EQPROOF $delimiter)
                (Cons $proof (Cons (TokC MM_DOT $dot) Nil))))))))
   (MMStatementTheorem
     (metamath-ledger:span $left $right)
     (metamath-ledger:label-value $label)
     (metamath-ledger:symbols $formula)
     (MMProofNormal (metamath-ledger:proof-labels $proof))))

(= (metamath-ledger:statement
      (NodeC statement_theorem_compressed statement $left $right
        (Cons $label
          (Cons (TokC MM_P $command)
            (Cons $formula
              (Cons (TokC MM_EQPROOF $delimiter)
                (Cons (TokC MM_LP $open)
                  (Cons $header
                    (Cons (TokC MM_RP $close)
                      (Cons $body (Cons (TokC MM_DOT $dot) Nil)))))))))))
   (MMStatementTheorem
     (metamath-ledger:span $left $right)
     (metamath-ledger:label-value $label)
     (metamath-ledger:symbols $formula)
     (MMProofCompressed
       (metamath-ledger:proof-header $header)
       (metamath-ledger:compressed-words $body))))

(= (metamath-ledger:statement
      (NodeC statement_include outer_statement $left $right
        (Cons (TokC MM_INCLUDE_OPEN $open)
          (Cons $path (Cons (TokC MM_INCLUDE_CLOSE $close) Nil)))))
   (MMStatementInclude
     (metamath-ledger:span $left $right)
     (metamath-ledger:include-value $path)))

; Inner statements either contribute one ordinary ledger entry or flatten a
; scoped block into explicit open/body/close entries.  The block itself is a
; statement in the authored grammar, so scope placement is no longer encoded
; by a second database grammar.
(= (metamath-ledger:inner-statement-entries $statement)
   (case $statement
     (((NodeC statement_block statement $left $right
         (Cons (TokC MM_SCOPE_OPEN $open)
           (Cons $inside (Cons (TokC MM_SCOPE_CLOSE $close) Nil))))
       (Cons
         (MMStatementScopeOpen (metamath-ledger:span $open (+ $open 1)))
         (metamath-ledger:append
           (metamath-ledger:database $inside)
           (Cons
             (MMStatementScopeClose
               (metamath-ledger:span $close (+ $close 1)))
             Nil))))
      ($ordinary (Cons (metamath-ledger:statement $ordinary) Nil)))))

(= (metamath-ledger:outer-statement-entries $statement)
   (case $statement
     (((NodeC outer_statement_inner outer_statement $left $right
         (Cons $inner Nil))
       (metamath-ledger:inner-statement-entries $inner))
      ($outer (Cons (metamath-ledger:statement $outer) Nil)))))

(= (metamath-ledger:database
      (NodeC database_empty database $left $right
        (Cons (EpsC) Nil)))
   Nil)
(= (metamath-ledger:database
      (NodeC database_more database $left $right
        (Cons $statement (Cons $rest Nil))))
   (metamath-ledger:append
     (metamath-ledger:inner-statement-entries $statement)
     (metamath-ledger:database $rest)))

(= (metamath-ledger:outer-database
      (NodeC outer_database_empty outer_database $left $right
        (Cons (EpsC) Nil)))
   Nil)
(= (metamath-ledger:outer-database
      (NodeC outer_database_more outer_database $left $right
        (Cons $statement (Cons $rest Nil))))
   (metamath-ledger:append
     (metamath-ledger:outer-statement-entries $statement)
     (metamath-ledger:outer-database $rest)))

(= (metamath-ledger:contains-include Nil) False)
(= (metamath-ledger:contains-include (Cons $statement $rest))
   (case $statement
     (((MMStatementInclude $span $path) True)
      ($other (metamath-ledger:contains-include $rest)))))

; Index the exact token ledger by the same boundary constructors used in the
; admitted grammar presentation.  The final boundary has no token payload.
(= (metamath-ledger:index-source-tokens $space Nil $index)
   (let $boundary-label (lib_parse:boundary-label $index)
     (let $added-boundary
       (add-atom $space
         (MMLedgerBoundaryIndex $boundary-label $index))
       True)))
(= (metamath-ledger:index-source-tokens
      $space (Cons $token $rest) $index)
   (let $boundary-label (lib_parse:boundary-label $index)
     (let $added-boundary
       (add-atom $space (MMLedgerBoundaryIndex $boundary-label $index))
       (let $added-token
         (add-atom $space
           (MMLedgerSourceToken $boundary-label $index $token))
         (metamath-ledger:index-source-tokens
           $space $rest (+ $index 1))))))

(= (metamath-ledger:boundary-index $space (PApp $boundary-label LNil))
   (case (collapse
           (match $space
             (MMLedgerBoundaryIndex $boundary-label $index)
             (MMFoundBoundaryIndex $index)))
     ((($only) $only)
      ($_ MMNoBoundaryIndex))))

(= (metamath-ledger:source-token $space (PApp $boundary-label LNil))
   (case (collapse
           (match $space
             (MMLedgerSourceToken $boundary-label $index $token)
             (MMFoundSourceToken $index $token)))
     ((($only) $only)
      ($_ MMNoSourceToken))))

; Resolve a generated production rule identity against the admitted grammar
; data itself.  No independent rule-name table is supplied by the caller.
(= (metamath-ledger:production-for-rule Nil $rule-id)
   MMNoProduction)
(= (metamath-ledger:production-for-rule
      (Cons (Prod $label $sort $template) $rest) $rule-id)
   (let $label-text (lib_parse:atom-text $label)
     (if (== $rule-id (lib_parse:rule-id "production" $label-text))
       (MMFoundProduction $label $sort)
       (metamath-ledger:production-for-rule $rest $rule-id))))
(= (metamath-ledger:production-for-rule
      (Cons (VarD $token $sort) $rest) $rule-id)
   (metamath-ledger:production-for-rule $rest $rule-id))
(= (metamath-ledger:production-for-rule
      (Cons (LexD $class $sort) $rest) $rule-id)
   (metamath-ledger:production-for-rule $rest $rule-id))

(= (metamath-ledger:dag-children-tree $space $grammar DrNil)
   (MMTreeChildrenOK Nil))
(= (metamath-ledger:dag-children-tree
      $space $grammar (DrCons $child-id $rest))
   (case (metamath-ledger:dag-node-tree $space $grammar $child-id)
     (((MMTreeOK $child)
       (case (metamath-ledger:dag-children-tree $space $grammar $rest)
         (((MMTreeChildrenOK $children)
           (MMTreeChildrenOK (Cons $child $children)))
          ($error $error))))
      ($error $error))))

; Reconstruct the parser tree from the exact accepted chronological DAG.
; Token and span payloads come from the identity-bound token index above.
(= (metamath-ledger:dag-node-tree $space $grammar $id)
   (case (gic-index-dag-node-lookup $space $id)
     (((FoundDagNode (GRuleInst $rule-id $arguments) $child-ids)
       (case (gic-index-dag-lookup $space $id)
         (((FoundDagValue
              (PApp "__lib_parse.Boundary"
                (LCons $source (LCons $boundary LNil))))
           (case (metamath-ledger:boundary-index $space $boundary)
             (((MMFoundBoundaryIndex $index) (MMTreeOK (EpsC)))
              ($error (MMTreeError missing-boundary-index)))))
          ((FoundDagValue
              (PApp "__lib_parse.TokenSpan"
                (LCons $source
                  (LCons $left (LCons $right (LCons $token-pattern LNil))))))
           (case (metamath-ledger:source-token $space $left)
             (((MMFoundSourceToken $index $token)
               (MMTreeOK (TokC $token $index)))
              ($error (MMTreeError missing-source-token)))))
          ((FoundDagValue
              (PApp "__lib_parse.GrammarDerivesNode"
                (LCons $source
                  (LCons $sort-pattern (LCons $left (LCons $right LNil))))))
           (case (metamath-ledger:production-for-rule $grammar $rule-id)
             (((MMFoundProduction $label $sort)
               (case (metamath-ledger:boundary-index $space $left)
                 (((MMFoundBoundaryIndex $left-index)
                   (case (metamath-ledger:boundary-index $space $right)
                     (((MMFoundBoundaryIndex $right-index)
                       (case (metamath-ledger:dag-children-tree
                               $space $grammar $child-ids)
                         (((MMTreeChildrenOK $children)
                           (MMTreeOK
                             (NodeC $label $sort $left-index $right-index
                               $children)))
                          ($error $error))))
                      ($error (MMTreeError missing-right-boundary)))))
                  ($error (MMTreeError missing-left-boundary)))))
              (MMNoProduction
               (case (MMLexicalLeaf $child-ids
                       (metamath-ledger:source-token $space $left)
                       (metamath-ledger:boundary-index $space $right))
                 (((MMLexicalLeaf DrNil
                      (MMFoundSourceToken $left-index $token)
                      (MMFoundBoundaryIndex $right-index))
                   (MMTreeOK
                     (LeafC $token $left-index $right-index)))
                  ($_ (MMTreeError malformed-lexical-leaf)))))
              ($error (MMTreeError malformed-production-lookup)))))
          ($error (MMTreeError unsupported-dag-judgment)))))
      ($error (MMTreeError missing-accepted-dag-node)))))

; There is one fixed grammar root.  Source identity is carried by the same
; CheckedSource package as the generated grammar presentation.
(= (metamath-ledger:source-package
      (MMSourceIdentityV0 $revision $digest) $presentation)
   (GSLTSourceV1
     (SourceIdentityV1 "Metamath" $revision $digest)
     (AssumptionLedgerV1 LNil)
     (ProfileLedgerV1
       (LCons
         (SourceProfileV1
           "ordered-statement-ledger" "v0"
           (PApp "__metamath.ordered-statement-ledger.v0" LNil))
         LNil))
     $presentation))

(= (metamath-ledger:checked-dag-ledger
      $space $revision $digest $tokens $parser-tree
      $goal $root $blocks $node-count)
   (if (gic-index-check-dag-blocks-valid
         $space $goal $root $blocks)
     (if (metamath-ledger:index-source-tokens $space $tokens 0)
       (case (metamath-ledger:dag-node-tree
               $space (lib_parse:mm-database-grammar) $root)
         (((MMTreeOK $checked-tree)
           (if (== $checked-tree $parser-tree)
             (let $entries (metamath-ledger:outer-database $checked-tree)
               (if (metamath-ledger:contains-include $entries)
                 (MMIncludeResolutionRequired
                   (MMSourceIdentityV0 $revision $digest)
                   (lp-len $tokens) $node-count $entries)
                 (MMCheckedStatementLedger
                   (MMSourceIdentityV0 $revision $digest)
                   (lp-len $tokens) $node-count $entries)))
             (MMStatementLedgerError
               checked-tree-disagrees-with-parser)))
          ($error
           (MMStatementLedgerError
             accepted-dag-tree-reconstruction-failed $error))))
       (MMStatementLedgerError token-index-failed))
     (MMStatementLedgerError checked-proof-rejected)))

(= (metamath-ledger:checked-lower
      (MMSourceIdentityV0 $revision $digest) $tokens $tree)
   (case (lib_parse:dag-presentation-candidate
           (lib_parse:mm-database-grammar) $digest $tokens)
     (((LPInferencePresentation
          (GPresentation $constructors $judgments $rules))
       (case (gparse:inference-dag-proof
               (lib_parse:mm-database-grammar)
               $digest outer_database $tokens $tree)
         (((LPInferenceDagBlocks $goal $root $blocks $node-count)
           ; Operationally destructure the one source package in place.  Deep
           ; generated presentations are not rewrapped or recopied between
           ; admission and checking.
           (let $identity
             (SourceIdentityV1 "Metamath" $revision $digest)
             (let $assumptions (AssumptionLedgerV1 LNil)
               (let $profiles
                 (ProfileLedgerV1
                   (LCons
                     (SourceProfileV1
                       "ordered-statement-ledger" "v0"
                       (PApp "__metamath.ordered-statement-ledger.v0" LNil))
                     LNil))
                 (if (and (gslt-identity-valid-v1 $identity)
                          (and (gslt-assumptions-valid-v1 $assumptions)
                               (gslt-profiles-valid-v1 $profiles)))
                   (case (gic-build-pathmap-index-parts
                           $constructors $judgments $rules)
                     (((GICIndexOK $space)
                       (metamath-ledger:checked-dag-ledger
                         $space $revision $digest $tokens $tree
                         $goal $root $blocks $node-count))
                      ($_
                       (MMStatementLedgerError
                         generated-presentation-rejected))))
                   (MMStatementLedgerError source-metadata-rejected))))))
          ($error $error))))
      ($error $error))))

; The scannerless parser is an untrusted certificate producer.  Its source
; digest must agree with the caller's identity, and the existing generic DAG
; checker above independently replays the complete token ledger and tree.
; ABI and forest digests remain attached to the certificate as provenance;
; neither is treated as proof of correctness.
(= (metamath-ledger:checked-gslt2parse-certificate
      (MMSourceIdentityV0 $revision $digest)
      (GSLT2ParseSourceCertificateV1
        $digest $source-bytes $abi-digest $forest-digest $tokens $tree))
   (metamath-ledger:checked-lower
     (MMSourceIdentityV0 $revision $digest) $tokens $tree))

(= (metamath-ledger:parse-source $grammar-path $identity $text)
   (case (lib_parse:mm-lex-string $text)
     (((Ok $tokens)
       (case (lib_parse:mm-parse-database-shared $grammar-path $tokens)
         (((Unique $tree)
           (metamath-ledger:checked-lower
             $identity $tokens $tree))
          (Ambiguous
           (MMStatementLedgerError ambiguous-source))
          (NoParse
           (MMStatementLedgerError source-does-not-derive))
          ($error $error))))
      ($error $error))))

(= (metamath-ledger:parse-file $grammar-path $identity $path)
   (case (fs:read-text $path)
     (((Error $call $reason)
       (MMStatementLedgerError source-read-failed $reason))
      ($text
       (metamath-ledger:parse-source
         $grammar-path $identity $text)))))

; Summary order:
; statements, constants, variables, disjoint declarations, floats,
; essentials, axioms, theorems, normal proofs, compressed proofs,
; scope opens, scope closes, includes.
(= (metamath-ledger:summary-add
      (MMLedgerCounts $all $constants $variables $disjoint $floats
        $essentials $axioms $theorems $normal $compressed
        $opens $closes $includes)
      (MMStatementConst $span $symbols))
   (MMLedgerCounts (+ $all 1) (+ $constants 1) $variables $disjoint
     $floats $essentials $axioms $theorems $normal $compressed
     $opens $closes $includes))
(= (metamath-ledger:summary-add
      (MMLedgerCounts $all $constants $variables $disjoint $floats
        $essentials $axioms $theorems $normal $compressed
        $opens $closes $includes)
      (MMStatementVar $span $symbols))
   (MMLedgerCounts (+ $all 1) $constants (+ $variables 1) $disjoint
     $floats $essentials $axioms $theorems $normal $compressed
     $opens $closes $includes))
(= (metamath-ledger:summary-add
      (MMLedgerCounts $all $constants $variables $disjoint $floats
        $essentials $axioms $theorems $normal $compressed
        $opens $closes $includes)
      (MMStatementDisjoint $span $symbols))
   (MMLedgerCounts (+ $all 1) $constants $variables (+ $disjoint 1)
     $floats $essentials $axioms $theorems $normal $compressed
     $opens $closes $includes))
(= (metamath-ledger:summary-add
      (MMLedgerCounts $all $constants $variables $disjoint $floats
        $essentials $axioms $theorems $normal $compressed
        $opens $closes $includes)
      (MMStatementFloat $span $label $typecode $variable))
   (MMLedgerCounts (+ $all 1) $constants $variables $disjoint
     (+ $floats 1) $essentials $axioms $theorems $normal $compressed
     $opens $closes $includes))
(= (metamath-ledger:summary-add
      (MMLedgerCounts $all $constants $variables $disjoint $floats
        $essentials $axioms $theorems $normal $compressed
        $opens $closes $includes)
      (MMStatementEssential $span $label $formula))
   (MMLedgerCounts (+ $all 1) $constants $variables $disjoint
     $floats (+ $essentials 1) $axioms $theorems $normal $compressed
     $opens $closes $includes))
(= (metamath-ledger:summary-add
      (MMLedgerCounts $all $constants $variables $disjoint $floats
        $essentials $axioms $theorems $normal $compressed
        $opens $closes $includes)
      (MMStatementAxiom $span $label $formula))
   (MMLedgerCounts (+ $all 1) $constants $variables $disjoint
     $floats $essentials (+ $axioms 1) $theorems $normal $compressed
     $opens $closes $includes))
(= (metamath-ledger:summary-add
      (MMLedgerCounts $all $constants $variables $disjoint $floats
        $essentials $axioms $theorems $normal $compressed
        $opens $closes $includes)
      (MMStatementTheorem $span $label $formula
        (MMProofNormal $proof)))
   (MMLedgerCounts (+ $all 1) $constants $variables $disjoint
     $floats $essentials $axioms (+ $theorems 1) (+ $normal 1) $compressed
     $opens $closes $includes))
(= (metamath-ledger:summary-add
      (MMLedgerCounts $all $constants $variables $disjoint $floats
        $essentials $axioms $theorems $normal $compressed
        $opens $closes $includes)
      (MMStatementTheorem $span $label $formula
        (MMProofCompressed $header $body)))
   (MMLedgerCounts (+ $all 1) $constants $variables $disjoint
     $floats $essentials $axioms (+ $theorems 1) $normal (+ $compressed 1)
     $opens $closes $includes))
(= (metamath-ledger:summary-add
      (MMLedgerCounts $all $constants $variables $disjoint $floats
        $essentials $axioms $theorems $normal $compressed
        $opens $closes $includes)
      (MMStatementScopeOpen $span))
   (MMLedgerCounts (+ $all 1) $constants $variables $disjoint
     $floats $essentials $axioms $theorems $normal $compressed
     (+ $opens 1) $closes $includes))
(= (metamath-ledger:summary-add
      (MMLedgerCounts $all $constants $variables $disjoint $floats
        $essentials $axioms $theorems $normal $compressed
        $opens $closes $includes)
      (MMStatementScopeClose $span))
   (MMLedgerCounts (+ $all 1) $constants $variables $disjoint
     $floats $essentials $axioms $theorems $normal $compressed
     $opens (+ $closes 1) $includes))
(= (metamath-ledger:summary-add
      (MMLedgerCounts $all $constants $variables $disjoint $floats
        $essentials $axioms $theorems $normal $compressed
        $opens $closes $includes)
      (MMStatementInclude $span $path))
   (MMLedgerCounts (+ $all 1) $constants $variables $disjoint
     $floats $essentials $axioms $theorems $normal $compressed
     $opens $closes (+ $includes 1)))

(= (metamath-ledger:summary-entries $counts Nil) $counts)
(= (metamath-ledger:summary-entries $counts (Cons $entry $rest))
   (metamath-ledger:summary-entries
     (metamath-ledger:summary-add $counts $entry) $rest))

(= (metamath-ledger:theorem-claims-entries Nil) Nil)
(= (metamath-ledger:theorem-claims-entries (Cons $entry $rest))
   (case $entry
     (((MMStatementTheorem $span $label $formula $proof)
       (Cons (MMTheoremClaim $label $formula)
         (metamath-ledger:theorem-claims-entries $rest)))
      ($other (metamath-ledger:theorem-claims-entries $rest)))))

(= (metamath-ledger:theorem-claims $result)
   (case $result
     (((MMCheckedStatementLedger $identity $tokens $nodes $entries)
       (metamath-ledger:theorem-claims-entries $entries))
      ((MMIncludeResolutionRequired $identity $tokens $nodes $entries)
       (metamath-ledger:theorem-claims-entries $entries))
      ($error $error))))

(= (metamath-ledger:overview $result)
   (case $result
     (((MMCheckedStatementLedger $identity $tokens $nodes $entries)
       (MMCheckedLedgerOverview $identity $tokens $nodes
         (metamath-ledger:summary-entries
           (MMLedgerCounts 0 0 0 0 0 0 0 0 0 0 0 0 0)
           $entries)
         (metamath-ledger:theorem-claims-entries $entries)))
      ((MMIncludeResolutionRequired $identity $tokens $nodes $entries)
       (MMIncludeLedgerOverview $identity $tokens $nodes
         (metamath-ledger:summary-entries
           (MMLedgerCounts 0 0 0 0 0 0 0 0 0 0 0 0 0)
           $entries)
         (metamath-ledger:theorem-claims-entries $entries)))
      ($error $error))))

(= (metamath-ledger:summary $result)
   (case $result
     (((MMCheckedStatementLedger $identity $tokens $nodes $entries)
       (MMCheckedLedgerSummary $identity $tokens $nodes
         (metamath-ledger:summary-entries
           (MMLedgerCounts 0 0 0 0 0 0 0 0 0 0 0 0 0)
           $entries)))
      ((MMIncludeResolutionRequired $identity $tokens $nodes $entries)
       (MMIncludeLedgerSummary $identity $tokens $nodes
         (metamath-ledger:summary-entries
           (MMLedgerCounts 0 0 0 0 0 0 0 0 0 0 0 0 0)
           $entries)))
      ($error $error))))
