; ============================================================================
; kernel_signature_lf_indexed_conversion_frontend_bridge_lib_v0.metta
;
; Proof-carrying conversion boundary for the indexed LF kernel.
;
; KWCheckConverted carries raw and normalized terms for both the candidate and
; its type, plus exact finite conversion proofs.  This bridge reconstructs the
; first-order conversion goals from the KW terms themselves, checks both proof
; trees through an admitted GSLT source, and only then invokes kw-kernel-check
; on the normalized pair.
;
; This profile is intentionally constant-free.  It covers the empty-signature
; Srt/Var/Pi/Lam/App fragment.  Constants fail closed until a source-bound name
; correspondence is supplied.
; ============================================================================

!(import! &self kernel_signature_lf_indexed_frontend_bridge_lib_v0.metta)
!(import! &self gslt_checked_source_v1.metta)

; ---------- KW term to first-order pattern correspondence ------------------

(= (lf-fo-encode-nat $index)
   (if (== $index 0)
     (PApp "Zero" LNil)
     (PApp "Succ"
       (LCons (lf-fo-encode-nat (- $index 1)) LNil))))

(= (lf-fo-encode-index $index)
   (if (binding-depth-ok $index)
     (LFPatternOK (lf-fo-encode-nat $index))
     LFPatternFail))

(= (lf-fo-encode-unary $head $encoded)
   (case $encoded
     (((LFPatternOK $value)
       (LFPatternOK (PApp $head (LCons $value LNil))))
      ($_ LFPatternFail))))

(= (lf-fo-encode-binary $head $left $right)
   (case (LFBinaryEncoding $left $right)
     (((LFBinaryEncoding
          (LFPatternOK $left-pattern)
          (LFPatternOK $right-pattern))
       (LFPatternOK
         (PApp $head
           (LCons $left-pattern (LCons $right-pattern LNil)))))
      ($_ LFPatternFail))))

(= (lf-fo-encode-term $term)
   (case $term
     (((Srt type)
       (LFPatternOK
         (PApp "Srt"
           (LCons (PApp "TypeSort" LNil) LNil))))
      ((Srt kind)
       (LFPatternOK
         (PApp "Srt"
           (LCons (PApp "KindSort" LNil) LNil))))
      ((Var $index)
       (lf-fo-encode-unary "Var" (lf-fo-encode-index $index)))
      ((Pi $domain $body)
       (lf-fo-encode-binary "Pi"
         (lf-fo-encode-term $domain)
         (lf-fo-encode-term $body)))
      ((Lam $domain $body)
       (lf-fo-encode-binary "Lam"
         (lf-fo-encode-term $domain)
         (lf-fo-encode-term $body)))
      ((App $function $argument)
       (lf-fo-encode-binary "App"
         (lf-fo-encode-term $function)
         (lf-fo-encode-term $argument)))
      ($_ LFPatternFail))))

(= (lf-fo-conversion-goal $source $target)
   (case
     (LFBinaryEncoding
       (lf-fo-encode-term $source)
       (lf-fo-encode-term $target))
     (((LFBinaryEncoding
          (LFPatternOK $source-pattern)
          (LFPatternOK $target-pattern))
       (LFGoalOK
         (PApp "Converts"
           (LCons $source-pattern (LCons $target-pattern LNil)))))
      ($_ LFGoalFail))))

; ---------- Source-indexed conversion checking -----------------------------

(= (lf-fo-conversion-check-with-source $source $raw $normalized $proof)
   (case (lf-fo-conversion-goal $raw $normalized)
     (((LFGoalOK $goal)
       (gslt-source-check-v1 $source $goal $proof))
      ($_ False))))

(= (lf-fo-conversion-check-dag-with-source
      $source $raw $normalized $root-id $nodes)
   (case (lf-fo-conversion-goal $raw $normalized)
     (((LFGoalOK $goal)
       (gslt-source-check-dag-v1 $source $goal $root-id $nodes))
      ($_ False))))

(= (lf-fo-conversion-check-dag-chunks-with-source
      $source $raw $normalized $root-id $chunks)
   (case (lf-fo-conversion-goal $raw $normalized)
     (((LFGoalOK $goal)
       (gslt-source-check-dag-chunks-indexed-v1
         $source $goal $root-id $chunks))
      ($_ False))))

(= (lf-fo-conversion-check-dag-streaming-with-source
      $source $raw $normalized $root-id $chunks)
   (case (lf-fo-conversion-goal $raw $normalized)
     (((LFGoalOK $goal)
       (gslt-source-check-dag-streaming-indexed-v1
         $source $goal $root-id $chunks))
      ($_ False))))

(= (lf-fo-conversion-check-dag-pure-streaming-with-source
      $source $raw $normalized $root-id $chunks)
   (case (lf-fo-conversion-goal $raw $normalized)
     (((LFGoalOK $goal)
       (gslt-source-check-dag-pure-streaming-v1
         $source $goal $root-id $chunks))
      ($_ False))))

(= (lf-fo-conversion-finish-dag-pure-streaming-with-source
      $source $raw $normalized $root-id $state)
   (case (lf-fo-conversion-goal $raw $normalized)
     (((LFGoalOK $goal)
       (gslt-source-finish-dag-pure-streaming-v1
         $source $state $goal $root-id))
      ($_ False))))

; ---------- Conversion-gated LF checking -----------------------------------

(= (kw-lf-fo-check-with-source $source $witness)
   (case $witness
     (((KWCheckConverted
          $signature
          $raw-term $normalized-term $term-proof
          $raw-type $normalized-type $type-proof)
       (if
         (lf-fo-conversion-check-with-source
           $source $raw-term $normalized-term $term-proof)
         (if
           (lf-fo-conversion-check-with-source
             $source $raw-type $normalized-type $type-proof)
           (kw-kernel-check
             (KWCheck $signature $normalized-term $normalized-type))
           (Err type-conversion-failed))
         (Err term-conversion-failed)))
      ($_ (Err bad-conversion-witness)))))

(= (kw-lf-fo-check-dag-with-source $source $witness)
   (case $witness
     (((KWCheckConvertedDAG
          $signature
          $raw-term $normalized-term $term-root-id $term-nodes
          $raw-type $normalized-type $type-root-id $type-nodes)
       (if
         (lf-fo-conversion-check-dag-with-source
           $source $raw-term $normalized-term $term-root-id $term-nodes)
         (if
           (lf-fo-conversion-check-dag-with-source
             $source $raw-type $normalized-type $type-root-id $type-nodes)
           (kw-kernel-check
             (KWCheck $signature $normalized-term $normalized-type))
           (Err type-conversion-failed))
         (Err term-conversion-failed)))
      ($_ (Err bad-conversion-dag-witness)))))

(= (kw-lf-fo-check-dag-chunks-with-source $source $witness)
   (case $witness
     (((KWCheckConvertedDAGChunks
          $signature
          $raw-term $normalized-term $term-root-id $term-chunks
          $raw-type $normalized-type $type-root-id $type-chunks)
       (if
         (lf-fo-conversion-check-dag-chunks-with-source
           $source $raw-term $normalized-term $term-root-id $term-chunks)
         (if
           (lf-fo-conversion-check-dag-chunks-with-source
             $source $raw-type $normalized-type $type-root-id $type-chunks)
           (kw-kernel-check
             (KWCheck $signature $normalized-term $normalized-type))
           (Err type-conversion-failed))
         (Err term-conversion-failed)))
      ($_ (Err bad-conversion-dag-chunks-witness)))))

(= (kw-lf-fo-check-dag-streaming-with-source $source $witness)
   (case $witness
     (((KWCheckConvertedStreamingDAGChunks
          $signature
          $raw-term $normalized-term $term-root-id $term-chunks
          $raw-type $normalized-type $type-root-id $type-chunks)
       (if
         (lf-fo-conversion-check-dag-streaming-with-source
           $source $raw-term $normalized-term $term-root-id $term-chunks)
         (if
           (lf-fo-conversion-check-dag-streaming-with-source
             $source $raw-type $normalized-type $type-root-id $type-chunks)
           (kw-kernel-check
             (KWCheck $signature $normalized-term $normalized-type))
           (Err type-conversion-failed))
         (Err term-conversion-failed)))
      ($_ (Err bad-conversion-streaming-dag-witness)))))

(= (kw-lf-fo-check-dag-pure-streaming-with-source $source $witness)
   (case $witness
     (((KWCheckConvertedStreamingDAGChunks
          $signature
          $raw-term $normalized-term $term-root-id $term-chunks
          $raw-type $normalized-type $type-root-id $type-chunks)
       (if
         (lf-fo-conversion-check-dag-pure-streaming-with-source
           $source $raw-term $normalized-term $term-root-id $term-chunks)
         (if
           (lf-fo-conversion-check-dag-pure-streaming-with-source
             $source $raw-type $normalized-type $type-root-id $type-chunks)
           (kw-kernel-check
             (KWCheck $signature $normalized-term $normalized-type))
           (Err type-conversion-failed))
         (Err term-conversion-failed)))
      ($_ (Err bad-conversion-pure-streaming-dag-witness)))))

; Process-bounded checking carries the unique pure checker state returned by
; each chronological chunk into the next worker.  Only the terminal states
; cross this boundary; both conversion goals are reconstructed from the raw
; and normalized KW terms before the indexed LF kernel is invoked.
(= (kw-lf-fo-check-dag-pure-stream-states-with-source
      $source
      $signature
      $raw-term $normalized-term $term-root-id $term-state
      $raw-type $normalized-type $type-root-id $type-state)
   (if
     (lf-fo-conversion-finish-dag-pure-streaming-with-source
       $source $raw-term $normalized-term $term-root-id $term-state)
     (if
       (lf-fo-conversion-finish-dag-pure-streaming-with-source
         $source $raw-type $normalized-type $type-root-id $type-state)
       (kw-kernel-check
         (KWCheck $signature $normalized-term $normalized-type))
       (Err type-conversion-state-failed))
     (Err term-conversion-state-failed)))
