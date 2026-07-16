!(import! &self gslt_checked_source_v1)

(= (gslt-fixture-identity-v1)
   (SourceIdentityV1
     "generic-inference-fixture" "v1" "sha256:fixture"))

(= (gslt-fixture-assumptions-v1) (AssumptionLedgerV1 LNil))

(= (gslt-fixture-profiles-v1)
   (ProfileLedgerV1
     (LCons
       (SourceProfileV1
         "proof-calculus" "v1" (PApp "ExactPremises" LNil))
       LNil)))

(= (gslt-fixture-source-v1)
   (GSLTSourceV1
     (gslt-fixture-identity-v1)
     (gslt-fixture-assumptions-v1)
     (gslt-fixture-profiles-v1)
     (gic-presentation)))

(= (gslt-fixture-source-with-presentation-v1 $presentation)
   (GSLTSourceV1
     (gslt-fixture-identity-v1)
     (gslt-fixture-assumptions-v1)
     (gslt-fixture-profiles-v1)
     $presentation))

(= (gslt-fixture-batch-v1)
   (CheckCons
     (GCheck (gic-proves (gic-B)) (gic-proof-b) True)
     (CheckCons
       (GCheck (gic-proves (gic-A)) (gic-proof-b) False)
       CheckNil)))

!(assertEqual
  (gslt-identity-valid-v1 (gslt-fixture-identity-v1)) True)

!(assertEqual
  (gslt-identity-valid-v1
    (SourceIdentityV1 "generic-inference-fixture" "v1" ""))
  False)

!(assertEqual
  (gslt-assumptions-valid-v1 (AssumptionLedgerV1 LNil)) True)

!(assertEqual
  (gslt-assumptions-valid-v1
    (AssumptionLedgerV1
      (LCons (SourceAssumptionV1 "a" (gic-A))
        (LCons (SourceAssumptionV1 "a" (gic-B)) LNil))))
  False)

!(assertEqual
  (gslt-profiles-valid-v1 (gslt-fixture-profiles-v1)) True)

!(assertEqual
  (gslt-profiles-valid-v1 (ProfileLedgerV1 LNil)) False)

!(assertEqual
  (gslt-profiles-valid-v1
    (ProfileLedgerV1
      (LCons (SourceProfileV1 "p" "v1" (gic-A))
        (LCons (SourceProfileV1 "p" "v2" (gic-B)) LNil))))
  False)

!(assertEqual
  (gslt-profiles-valid-v1
    (ProfileLedgerV1
      (LCons
        (SourceProfileV1 "p" "v1" (PLam (BSome "x") (Var 0)))
        LNil)))
  False)

!(assertEqual
  (gslt-source-validation-v1 (gslt-fixture-source-v1))
  SourceAcceptedV1)

!(assertEqual
  (gslt-source-validation-v1
    (GSLTSourceV1
      (SourceIdentityV1 "generic-inference-fixture" "v1" "")
      (gslt-fixture-assumptions-v1)
      (gslt-fixture-profiles-v1)
      (gic-presentation)))
  (SourceRejectedV1 InvalidIdentityV1))

!(assertEqual
  (gslt-source-validation-v1
    (GSLTSourceV1
      (gslt-fixture-identity-v1)
      (gslt-fixture-assumptions-v1)
      (ProfileLedgerV1 LNil)
      (gic-presentation)))
  (SourceRejectedV1 MissingProfileV1))

!(assertEqual
  (gslt-source-validation-v1
    (gslt-fixture-source-with-presentation-v1
      (GPresentation (gic-constructors) (gic-judgments)
        (LCons (gic-ax-a) (LCons (gic-ax-a) LNil)))))
  (SourceRejectedV1 InvalidPresentationV1))

!(assertEqual
  (gslt-source-check-v1
    (gslt-fixture-source-v1) (gic-proves (gic-B)) (gic-proof-b))
  True)

!(assertEqual
  (gslt-source-check-v1
    (gslt-fixture-source-v1) (gic-proves (gic-A)) (gic-proof-b))
  False)

!(assertEqual
  (gslt-source-check-v1
    SourceAcceptedV1 (gic-proves (gic-B)) (gic-proof-b))
  False)

!(assertEqual
  (gslt-source-check-batch-v1
    (gslt-fixture-source-v1) (gslt-fixture-batch-v1))
  True)

!(assertEqual
  (gslt-source-check-dag-v1
    (gslt-fixture-source-v1) (gic-proves (gic-B)) "b" (gic-proof-dag))
  True)

!(assertEqual
  (gslt-source-check-dag-v1
    (gslt-fixture-source-v1) (gic-proves (gic-A)) "b" (gic-proof-dag))
  False)

!(assertEqual
  (gslt-source-check-dag-indexed-v1
    (gslt-fixture-source-v1) (gic-proves (gic-B)) "b" (gic-proof-dag))
  True)

!(assertEqual
  (gslt-source-check-dag-chunks-indexed-v1
    (gslt-fixture-source-v1) (gic-proves (gic-B)) "b"
    (gic-proof-dag-chunks))
  True)

!(assertEqual
  (gslt-source-check-dag-terminal-indexed-v1
    (gslt-fixture-source-v1) (gic-proves (gic-B))
    (DcCons
      (DnCons (GDNode "a" (GRuleInst "ax-a" LNil) DrNil)
        (DnCons (GDNode "imp" (GRuleInst "ax-imp-ab" LNil) DrNil) DnNil))
      DcNil)
    (GDNode "b"
      (GRuleInst "mp" (LCons (gic-A) (LCons (gic-B) LNil)))
      (DrCons "a" (DrCons "imp" DrNil))))
  True)

!(assertEqual
  (gslt-source-check-trace-indexed-v1
    (gslt-fixture-source-v1)
    (TraceCheckCons
      (GTraceCheck (gic-proves (gic-B)) (gic-proof-b-trace) True)
      (TraceCheckCons
        (GTraceCheck (gic-proves (gic-A))
          (GaCons (GRef 0) GaNil) False)
        TraceCheckNil)))
  True)

!(assertEqual
  (gslt-source-check-trace-pathmap-v1
    (gslt-fixture-source-v1)
    (TraceCheckCons
      (GTraceCheck (gic-proves (gic-B)) (gic-proof-b-trace) True)
      (TraceCheckCons
        (GTraceCheck (gic-proves (gic-A))
          (GaCons (GRef 0) GaNil) False)
        TraceCheckNil)))
  False)

!(assertEqual
  (gslt-source-run-v1 (gslt-fixture-source-v1) UnsupportedOperationV1)
  False)

!(GSLTSourceV1Summary 24 24 0)
