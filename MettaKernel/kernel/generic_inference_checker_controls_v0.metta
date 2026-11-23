; Regression checks for the generic inference checker.
!(import! &self generic_inference_checker_v0)

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

!(assertEqual
  (gic-check (gic-language)
    (gic-proves (PSubst (Var 0) (gic-A)))
    (GProof
      (GRuleInst "subst" (LCons (Var 0) (LCons (gic-A) LNil))) PrNil))
  True)

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

!(assertEqual
  (gic-check-batch (gic-language)
    (CheckCons
      (GCheck (gic-proves (gic-B)) (gic-proof-b) True)
      (CheckCons
        (GCheck (gic-proves (gic-A)) (gic-proof-b) False)
        CheckNil)))
  True)

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

!(assertEqual
  (gic-check-dag-streaming-indexed
    (gic-language) (gic-proves (gic-B)) 2
    (gic-proof-dag-streaming-chunks))
  True)

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

!(GICChecksFinished 51)
