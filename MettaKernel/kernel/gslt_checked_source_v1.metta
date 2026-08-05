; =============================================================================
; gslt_checked_source_v1.metta
;
; Pure operational GSLT source admission over the generic inference checker.
;
; A source package carries identity, assumptions, profiles, and one inference
; presentation. Every public operation validates that exact package again;
; there is no capability atom or reusable admission token. Source identity is
; recorded data, not an authenticity oracle. A source adapter and its adequacy
; result remain responsible for relating the package to an independent source.
; =============================================================================

!(import! &self generic_inference_checker_v0)

; Source package:
;   (GSLTSourceV1 identity assumptions profiles presentation)
;   (SourceIdentityV1 system revision artifact-digest)
;   (AssumptionLedgerV1 entries)
;   (SourceAssumptionV1 id statement)
;   (ProfileLedgerV1 entries)
;   (SourceProfileV1 name version payload)

; ---------- Source identity -------------------------------------------------
(= (gslt-identity-valid-v1 $identity)
   (case $identity
     (((SourceIdentityV1 $system $revision $digest)
       (if (== $system "") False
         (if (== $revision "") False
           (if (== $digest "") False True))))
      ($_ False))))

; ---------- Assumption ledger ----------------------------------------------
(= (gslt-assumption-id-v1 (SourceAssumptionV1 $id $statement)) $id)

(= (gslt-assumption-ids-v1 LNil) LNil)
(= (gslt-assumption-ids-v1 (LCons $entry $rest))
   (LCons (gslt-assumption-id-v1 $entry)
     (gslt-assumption-ids-v1 $rest)))

(= (gslt-assumption-entry-valid-v1 $entry)
   (case $entry
     (((SourceAssumptionV1 $id $statement)
       (if (== $id "") False
         (if (gic-scoped-at 0 $statement)
           (gic-canonical $statement)
           False)))
      ($_ False))))

(= (gslt-assumption-entries-valid-v1 LNil) True)
(= (gslt-assumption-entries-valid-v1 (LCons $entry $rest))
   (if (gslt-assumption-entry-valid-v1 $entry)
     (gslt-assumption-entries-valid-v1 $rest)
     False))

(= (gslt-assumptions-valid-v1 $ledger)
   (case $ledger
     (((AssumptionLedgerV1 $entries)
       (if (gslt-assumption-entries-valid-v1 $entries)
         (gic-no-duplicates (gslt-assumption-ids-v1 $entries))
         False))
      ($_ False))))

; ---------- Profile ledger --------------------------------------------------
(= (gslt-profile-name-v1 (SourceProfileV1 $name $version $payload)) $name)

(= (gslt-profile-names-v1 LNil) LNil)
(= (gslt-profile-names-v1 (LCons $entry $rest))
   (LCons (gslt-profile-name-v1 $entry)
     (gslt-profile-names-v1 $rest)))

(= (gslt-profile-entry-valid-v1 $entry)
   (case $entry
     (((SourceProfileV1 $name $version $payload)
       (if (== $name "") False
         (if (== $version "") False
           (if (gic-scoped-at 0 $payload)
             (gic-canonical $payload)
             False))))
      ($_ False))))

(= (gslt-profile-entries-valid-v1 LNil) True)
(= (gslt-profile-entries-valid-v1 (LCons $entry $rest))
   (if (gslt-profile-entry-valid-v1 $entry)
     (gslt-profile-entries-valid-v1 $rest)
     False))

(= (gslt-profiles-empty-v1 $ledger)
   (case $ledger
     (((ProfileLedgerV1 LNil) True)
      ((ProfileLedgerV1 (LCons $entry $rest)) False)
      ($_ True))))

(= (gslt-profiles-valid-v1 $ledger)
   (case $ledger
     (((ProfileLedgerV1 LNil) False)
      ((ProfileLedgerV1 (LCons $entry $rest))
       (let $entries (LCons $entry $rest)
         (if (gslt-profile-entries-valid-v1 $entries)
           (gic-no-duplicates (gslt-profile-names-v1 $entries))
           False)))
      ($_ False))))

; ---------- Package admission ----------------------------------------------
(= (gslt-source-validation-v1 $source)
   (case $source
     (((GSLTSourceV1 $identity $assumptions $profiles $presentation)
       (if (gslt-identity-valid-v1 $identity)
         (if (gslt-assumptions-valid-v1 $assumptions)
           (if (gslt-profiles-empty-v1 $profiles)
             (SourceRejectedV1 MissingProfileV1)
             (if (gslt-profiles-valid-v1 $profiles)
               (if (gic-presentation-valid $presentation)
                 SourceAcceptedV1
                 (SourceRejectedV1 InvalidPresentationV1))
               (SourceRejectedV1 InvalidProfileLedgerV1)))
           (SourceRejectedV1 InvalidAssumptionLedgerV1))
         (SourceRejectedV1 InvalidIdentityV1)))
      ($_ (SourceRejectedV1 MalformedSourceV1)))))

(= (gslt-source-valid-v1 $source)
   (== (gslt-source-validation-v1 $source) SourceAcceptedV1))

; ---------- Source-indexed checker operations ------------------------------
(= (gslt-presentation-run-v1 $presentation $operation)
   (case $operation
     (((SourceTreeCheckV1 $goal $proof)
       (gic-check $presentation $goal $proof))
      ((SourceBatchCheckV1 $checks)
       (gic-check-batch $presentation $checks))
      ((SourceDagCheckV1 $goal $root-id $nodes)
       (gic-check-dag $presentation $goal $root-id $nodes))
      ((SourceDagIndexedCheckV1 $goal $root-id $nodes)
       (gic-check-dag-indexed $presentation $goal $root-id $nodes))
      ((SourceDagChunksIndexedCheckV1 $goal $root-id $chunks)
       (gic-check-dag-chunks-indexed $presentation $goal $root-id $chunks))
      ((SourceDagStreamingIndexedCheckV1 $goal $root-id $chunks)
       (gic-check-dag-streaming-indexed
         $presentation $goal $root-id $chunks))
      ((SourceDagPureStreamingCheckV1 $goal $root-id $chunks)
       (gic-check-dag-pure-streaming
         $presentation $goal $root-id $chunks))
      ((SourceDagPureStreamingStepV1 $state $nodes)
       (gic-check-dag-pure-stream-step
         $presentation $state $nodes))
      ((SourceDagPureStreamingFinishV1 $state $goal $root-id)
       (gic-finish-dag-pure-stream $state $goal $root-id))
      ((SourceDagTerminalIndexedCheckV1 $goal $prefix-chunks $terminal)
       (gic-check-dag-terminal-indexed
         $presentation $goal $prefix-chunks $terminal))
      ((SourceTraceIndexedCheckV1 $checks)
       (gic-check-trace-indexed $presentation $checks))
      ((SourceTracePathMapCheckV1 $checks)
       (gic-check-trace-pathmap $presentation $checks))
      ($_ False))))

(= (gslt-source-run-v1 $source $operation)
   (if (gslt-source-valid-v1 $source)
     (case $source
       (((GSLTSourceV1 $identity $assumptions $profiles $presentation)
         (gslt-presentation-run-v1 $presentation $operation))
        ($_ False)))
     False))

(= (gslt-source-check-v1 $source $goal $proof)
   (gslt-source-run-v1 $source (SourceTreeCheckV1 $goal $proof)))

(= (gslt-source-check-batch-v1 $source $checks)
   (gslt-source-run-v1 $source (SourceBatchCheckV1 $checks)))

(= (gslt-source-check-dag-v1 $source $goal $root-id $nodes)
   (gslt-source-run-v1 $source
     (SourceDagCheckV1 $goal $root-id $nodes)))

(= (gslt-source-check-dag-indexed-v1 $source $goal $root-id $nodes)
   (gslt-source-run-v1 $source
     (SourceDagIndexedCheckV1 $goal $root-id $nodes)))

(= (gslt-source-check-dag-chunks-indexed-v1
      $source $goal $root-id $chunks)
   (gslt-source-run-v1 $source
     (SourceDagChunksIndexedCheckV1 $goal $root-id $chunks)))

(= (gslt-source-check-dag-streaming-indexed-v1
      $source $goal $root-id $chunks)
   (gslt-source-run-v1 $source
     (SourceDagStreamingIndexedCheckV1 $goal $root-id $chunks)))

(= (gslt-source-check-dag-pure-streaming-v1
      $source $goal $root-id $chunks)
   (gslt-source-run-v1 $source
     (SourceDagPureStreamingCheckV1 $goal $root-id $chunks)))

(= (gslt-source-step-dag-pure-streaming-v1
      $source $state $nodes)
   (gslt-source-run-v1 $source
     (SourceDagPureStreamingStepV1 $state $nodes)))

(= (gslt-source-finish-dag-pure-streaming-v1
      $source $state $goal $root-id)
   (gslt-source-run-v1 $source
     (SourceDagPureStreamingFinishV1 $state $goal $root-id)))

(= (gslt-source-check-dag-terminal-indexed-v1
      $source $goal $prefix-chunks $terminal)
   (gslt-source-run-v1 $source
     (SourceDagTerminalIndexedCheckV1 $goal $prefix-chunks $terminal)))

(= (gslt-source-check-trace-indexed-v1 $source $checks)
   (gslt-source-run-v1 $source (SourceTraceIndexedCheckV1 $checks)))

(= (gslt-source-check-trace-pathmap-v1 $source $checks)
   (gslt-source-run-v1 $source (SourceTracePathMapCheckV1 $checks)))
